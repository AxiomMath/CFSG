module

public import CFSG.Walter.W67.Section5.Borel54
public import CFSG.Walter.W67.Section5.Lemma53

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

namespace Sec54

theorem card_le_two {X : Subgroup G} {J : G} (hJX : J ∈ X) (hoJ : orderOf J = 2)
    (h : ∀ W : Subgroup G, W ≤ X → J ∈ W → IsPGroup 2 W → W ≤ Subgroup.zpowers J) :
    ∀ W : Subgroup G, W ≤ X → IsPGroup 2 W → Nat.card W ≤ 2 := by
  intro W hWX hW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J' : X := ⟨J, hJX⟩
  have hJ'p : IsPGroup 2 (Subgroup.zpowers J') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hoJ, pow_one]
  obtain ⟨S₂, hS₂⟩ := hJ'p.exists_le_sylow
  have hS₂card : Nat.card S₂ ≤ 2 := by
    have hle := h ((S₂ : Subgroup X).map X.subtype) (Subgroup.map_subtype_le _)
      ⟨J', hS₂ (Subgroup.mem_zpowers J'), rfl⟩ (S₂.isPGroup'.map _)
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hoJ] at this
  have hW' : IsPGroup 2 (W.subgroupOf X) :=
    hW.comap_of_injective X.subtype X.subtype_injective
  obtain ⟨S₁, hS₁⟩ := hW'.exists_le_sylow
  have h1 : Nat.card S₁ = Nat.card S₂ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  calc Nat.card W = Nat.card (W.subgroupOf X) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv).symm
    _ ≤ Nat.card S₁ := Subgroup.card_le_of_le hS₁
    _ = Nat.card S₂ := h1
    _ ≤ 2 := hS₂card

theorem exists_conj {D : Subgroup G} {J x : G} (hJD : J ∈ D) (hoJ : orderOf J = 2)
    (hD : ∀ W : Subgroup G, W ≤ D → IsPGroup 2 W → Nat.card W ≤ 2)
    (hx : x * J * x⁻¹ ∈ D) : ∃ d ∈ D, d * J * d⁻¹ = x * J * x⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J₁ : D := ⟨J, hJD⟩
  set J₂ : D := ⟨x * J * x⁻¹, hx⟩
  have hoJ₁ : orderOf J₁ = 2 := by rw [Subgroup.orderOf_mk, hoJ]
  have hoJ₂ : orderOf J₂ = 2 := by rw [Subgroup.orderOf_mk, orderOf_conj_mul, hoJ]
  have hS : ∀ y : D, orderOf y = 2 → ∃ S : Sylow 2 D, (S : Subgroup D) = Subgroup.zpowers y := by
    intro y hy
    have hp : IsPGroup 2 (Subgroup.zpowers y) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hy, pow_one]
    obtain ⟨S, hSle⟩ := hp.exists_le_sylow
    refine ⟨S, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [Nat.card_zpowers, hy]
    have := hD ((S : Subgroup D).map D.subtype) (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  obtain ⟨S₁, hS₁⟩ := hS J₁ hoJ₁
  obtain ⟨S₂, hS₂⟩ := hS J₂ hoJ₂
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq D S₁ S₂
  have hmem : d * J₁ * d⁻¹ ∈ Subgroup.zpowers J₂ := by
    rw [← hS₂, ← hd, Sylow.coe_subgroup_smul, hS₁]
    exact ⟨J₁, Subgroup.mem_zpowers J₁, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hoJ₂ hmem with h1 | h1
  · exfalso
    have : J₁ = 1 := by
      have := congrArg (fun z => d⁻¹ * z * d) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hoJ₁
    exact absurd hoJ₁ (by norm_num)
  · refine ⟨d, d.2, ?_⟩
    have := congrArg Subtype.val h1
    simpa using this

omit [Finite G] in
theorem card_sup_eq_mul {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G))
    (h : A ⊓ C = ⊥) : Nat.card (A ⊔ C : Subgroup G) = Nat.card A * Nat.card C := by
  set AC := A ⊔ C
  have hAn : (A.subgroupOf AC).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hC
  let π : AC →* AC ⧸ A.subgroupOf AC := QuotientGroup.mk' _
  have hbij : Function.Bijective (π.comp (Subgroup.inclusion (le_sup_right : C ≤ AC))) := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro c hc
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hc
      have hk : ((Subgroup.inclusion (le_sup_right : C ≤ AC) c : AC) : G) ∈ A :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf AC) _).mp hc
      have : (c : G) ∈ A ⊓ C := Subgroup.mem_inf.mpr ⟨hk, c.2⟩
      rw [h, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact Subtype.ext this
    · intro q
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨a, ha, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hC).mp hy
      refine ⟨⟨c, hc⟩, ?_⟩
      change ((⟨c, _⟩ : AC) : AC ⧸ A.subgroupOf AC) = ((⟨a * c, hy⟩ : AC) : AC ⧸ _)
      rw [QuotientGroup.eq]
      change c⁻¹ * (a * c) ∈ A
      have := (Subgroup.mem_normalizer_iff.mp (hC (C.inv_mem hc)) a).mp ha
      simpa [mul_assoc] using this
  have h1 := Nat.card_eq_of_bijective _ hbij
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf AC)
  rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv] at h2
  rw [h2, mul_comm]

theorem mem_normalizer_inf {A C : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hC : x ∈ Subgroup.normalizer (C : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  obtain ⟨hyA, hyC⟩ := Subgroup.mem_inf.mp hy
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hA y).mp hyA,
    (Subgroup.mem_normalizer_iff.mp hC y).mp hyC⟩

theorem mem_normalizer_centralizer {R : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (R : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  apply Sec53.mem_normalizer_of_conj_le
  intro y hy
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro r hr
  have hr' : x⁻¹ * r * x⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) r).mp hr
  have := hy _ hr'
  calc r * (x * y * x⁻¹) = x * ((x⁻¹ * r * x⁻¹⁻¹) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * r * x⁻¹⁻¹)) * x⁻¹ := by rw [this]
    _ = x * y * x⁻¹ * r := by group

theorem mem_normalizer_centralizer_singleton {u x : G}
    (hx : x ∈ Subgroup.centralizer ({u} : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer ({u} : Set G) : Set G) :=
  Subgroup.centralizer_le_normalizer _ hx |> fun h => by
    apply Sec53.mem_normalizer_of_conj_le
    intro y hy
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy) (Subgroup.inv_mem _ hx)

end Sec54

open Frame5 Borel5 CFSG.ProperTwoGeneratedCore
  CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator in
theorem lemma_5_4_of
    (h22 : S_lemma_2_2) (h26i : S_lemma_2_6_i) : S_lemma_5_4 := by
  intro G _ _ s hp f5 P hPel hP1 hJBE hirr
  set JBE := Subgroup.zpowers s.J ⊔ f5.B ⊔ s.fr.E with hJBEdef
  set NP := Subgroup.normalizer (P : Set G) with hNPdef
  have hJN : s.J ∈ NP := hJBE (Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (Subgroup.mem_zpowers _)))
  have hBN : f5.B ≤ NP := fun b hb => hJBE (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
  have hEN : s.fr.E ≤ NP := fun e he => hJBE (Subgroup.mem_sup_right he)
  have hirr' : ∀ Q : Subgroup G, Q ≤ P → s.J ∈ Subgroup.normalizer (Q : Set G) →
      f5.B ≤ Subgroup.normalizer (Q : Set G) → s.fr.E ≤ Subgroup.normalizer (Q : Set G) →
      Q = ⊥ ∨ Q = P := by
    intro Q hQP hJ hB hE
    exact hirr Q hQP (sup_le (sup_le (Subgroup.zpowers_le.mpr hJ) hB) hE)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP3 : IsPGroup 3 P := IsElementaryAbelian.isPGroup 3 P
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : P) ⟨y, hy⟩)
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
    rw [hk]
    exact Odd.pow (by decide)
  have hP3el : ∀ y ∈ P, y ^ (3 ^ (Nat.card P).factorization 3) = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
    have := pow_card_eq_one' (x := (⟨y, hy⟩ : P))
    rw [hk] at this
    rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
    exact congrArg Subtype.val this
  obtain ⟨g, hP₁g, hBg⟩ := f5.exists_std
  have hB₁ : f5.B = img s g (torus _) := hBg
  have hB₂ : f5.B = img s (g * weyl _) (torus _) := by rw [img_torus_weyl]; exact hB₁
  have hBK : f5.B ≤ s.K := f5.B_le
  have hCPN : Subgroup.centralizer (P : Set G) ≤ NP := Subgroup.centralizer_le_normalizer _
  set D := Subgroup.centralizer (P : Set G) ⊔ Subgroup.zpowers s.J with hDdef
  have hJD : s.J ∈ D := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hJnC : Subgroup.zpowers s.J ≤ Subgroup.normalizer
      (Subgroup.centralizer (P : Set G) : Set G) :=
    Subgroup.zpowers_le.mpr (Sec54.mem_normalizer_centralizer hJN)
  have key : (∀ W : Subgroup G, W ≤ D → IsPGroup 2 W → Nat.card W ≤ 2) →
      (∀ x ∈ NP, x * s.J * x⁻¹ ∈ D) →
      (NP ⊓ s.K ≤ img s g (unip _ ⊔ torus _) ∨
        NP ⊓ s.K ≤ img s (g * weyl _) (unip _ ⊔ torus _)) →
      NP ≤ JBE ⊔ Subgroup.centralizer (P : Set G) := by
    intro hD hxD hNK
    have hRC : ∀ h : PSL(2, GaloisField s.p s.f), f5.B = img s h (torus _) →
        NP ⊓ s.K ≤ img s h (unip _ ⊔ torus _) →
        NP ⊓ img s h (unip _) ≤ Subgroup.centralizer (P : Set G) := by
      intro h hBh hNKh
      set R := img s h (unip _) with hRdef
      have hRK : R ≤ s.K := img_le_K h _
      have hBR : f5.B ≤ Subgroup.normalizer (R : Set G) := by
        intro b hb
        rw [hBh] at hb
        obtain ⟨t, ht, rfl⟩ := mem_img.mp hb
        apply Sec53.mem_normalizer_of_conj_le
        intro y hy
        obtain ⟨u, hu, rfl⟩ := mem_img.mp hy
        refine mem_img.mpr ⟨t * u * t⁻¹, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (torus_le_normalizer_unip ht) u).mp hu
        · rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
      set R₀ := NP ⊓ R
      have hR₀B : ∀ b ∈ f5.B, ∀ v ∈ R₀, b * v * b⁻¹ ∈ R₀ := by
        intro b hb v hv
        exact (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_inf
          (Subgroup.le_normalizer (hBN hb)) (hBR hb)) v).mp hv
      rcases f5.irred hBh (V := R₀) inf_le_right hR₀B with h0 | h0
      · rw [h0]
        exact bot_le
      ·
        have hRN : R ≤ NP := fun r hr => by
          have : r ∈ R₀ := by rw [h0]; exact hr
          exact (Subgroup.mem_inf.mp this).1
        have hR3 : IsPGroup 3 R := by
          apply IsPGroup.of_card (n := s.f)
          rw [card_img, psl2UpperUnipotentSubgroup_card, GaloisField.card s.p s.f s.f_pos.ne', hp]
        obtain ⟨y, hyP, hy1, hyR⟩ := exists_fixed_ne_one hR3 hP3 hP1 hRN
        have hER : s.fr.E ≤ Subgroup.normalizer (R : Set G) := by
          intro e he
          apply Sec53.mem_normalizer_of_conj_le
          intro r hr
          have h1 : e * r * e⁻¹ ∈ NP ⊓ s.K := Subgroup.mem_inf.mpr
            ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hEN he)) r).mp (hRN hr),
              (Subgroup.mem_normalizer_iff.mp (s.fr.E_le_normalizer_K he) r).mp (hRK hr)⟩
          have hconj : (R.map (MulAut.conj e).toMonoidHom) ≤ R :=
            le_img_unip_of_isPGroup hp h (hR3.map _) (by
              rintro _ ⟨r', hr', rfl⟩
              exact hNKh (Subgroup.mem_inf.mpr
                ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hEN he)) r').mp
                  (hRN hr'),
                  (Subgroup.mem_normalizer_iff.mp (s.fr.E_le_normalizer_K he) r').mp (hRK hr')⟩))
          exact hconj ⟨r, hr, rfl⟩
        set CPR := P ⊓ Subgroup.centralizer (R : Set G)
        have hJR : s.J ∈ Subgroup.centralizer (R : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro r hr
          exact s.commute_J (s.K_le_H (hRK hr))
        rcases hirr' CPR inf_le_left
          (Sec54.mem_normalizer_inf hJN (Sec54.mem_normalizer_centralizer
            (Subgroup.centralizer_le_normalizer _ hJR)))
          (fun b hb => Sec54.mem_normalizer_inf (hBN hb)
            (Sec54.mem_normalizer_centralizer (hBR hb)))
          (fun e he => Sec54.mem_normalizer_inf (hEN he)
            (Sec54.mem_normalizer_centralizer (hER he))) with h1 | h1
        · exfalso
          have : y ∈ CPR := Subgroup.mem_inf.mpr ⟨hyP, by
            rw [Subgroup.mem_centralizer_iff]
            intro r hr
            have := hyR r hr
            calc r * y = r * y * r⁻¹ * r := by group
              _ = y * r := by rw [this]⟩
          rw [h1, Subgroup.mem_bot] at this
          exact hy1 this
        · intro r hr
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          have hzC : z ∈ CPR := by rw [h1]; exact hz
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzC).2 r
            (Subgroup.mem_inf.mp hr).2).symm
    have hRC' : ∀ k ∈ NP ⊓ s.K, k ∈ JBE ⊔ Subgroup.centralizer (P : Set G) := by
      intro k hk
      have hcase : ∀ h : PSL(2, GaloisField s.p s.f), f5.B = img s h (torus _) →
          NP ⊓ s.K ≤ img s h (unip _ ⊔ torus _) → k ∈ JBE ⊔ Subgroup.centralizer (P : Set G) := by
        intro h hBh hNKh
        have hk' := hNKh hk
        rw [img_sup, ← hBh] at hk'
        have hBR : f5.B ≤ Subgroup.normalizer ((img s h (unip _)) : Set G) := by
          intro b hb
          rw [hBh] at hb
          obtain ⟨t, ht, rfl⟩ := mem_img.mp hb
          apply Sec53.mem_normalizer_of_conj_le
          intro y hy
          obtain ⟨u, hu, rfl⟩ := mem_img.mp hy
          refine mem_img.mpr ⟨t * u * t⁻¹, ?_, ?_⟩
          · exact (Subgroup.mem_normalizer_iff.mp (torus_le_normalizer_unip ht) u).mp hu
          · rw [← map_inv, ← map_mul, ← map_mul]
            congr 1
            group
        obtain ⟨r, hr, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBR).mp hk'
        have hrN : r ∈ NP := by
          have := NP.mul_mem (Subgroup.mem_inf.mp hk).1 (NP.inv_mem (hBN hb))
          rwa [mul_inv_cancel_right] at this
        have hrC := hRC h hBh hNKh (Subgroup.mem_inf.mpr ⟨hrN, hr⟩)
        exact mul_mem (Subgroup.mem_sup_right hrC)
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
      rcases hNK with h1 | h1
      · exact hcase g hB₁ h1
      · exact hcase _ hB₂ h1
    intro x hx
    obtain ⟨d, hdD, hd⟩ := Sec54.exists_conj hJD s.orderOf_J hD (hxD x hx)
    obtain ⟨c, hc, j, hj, rfl⟩ := (mem_sup_iff_of_le_normalizer hJnC).mp hdD
    have hjJ : j * s.J = s.J * j := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hj
      exact (Commute.zpow_self s.J i).eq
    have hcJ : c * s.J * c⁻¹ = x * s.J * x⁻¹ := by
      rw [← hd]
      calc c * s.J * c⁻¹ = c * (j * s.J * j⁻¹) * c⁻¹ := by rw [hjJ, mul_inv_cancel_right]
        _ = c * j * s.J * (c * j)⁻¹ := by group
    set n := c⁻¹ * x
    have hnH : n ∈ s.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : n * s.J * n⁻¹ = s.J := by
        simp only [n]
        calc c⁻¹ * x * s.J * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * s.J * x⁻¹) * c := by group
          _ = c⁻¹ * (c * s.J * c⁻¹) * c := by rw [hcJ]
          _ = s.J := by group
      calc n * s.J = n * s.J * n⁻¹ * n := by group
        _ = s.J * n := by rw [this]
    have hnN : n ∈ NP := NP.mul_mem (NP.inv_mem (hCPN hc)) hx
    obtain ⟨j', hj', m, hm, hnjm⟩ := s.fr.exists_decomp_H_JM hnH
    have hmN : m ∈ NP := by
      have h1 : m = j'⁻¹ * n := by rw [hnjm]; group
      rw [h1]
      exact NP.mul_mem (NP.inv_mem (Subgroup.zpowers_le.mpr hJN hj')) hnN
    obtain ⟨k, hkK, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer s.fr.E_le_normalizer_K).mp hm
    have hkN : k ∈ NP := by
      have := NP.mul_mem hmN (NP.inv_mem (hEN he))
      rwa [mul_inv_cancel_right] at this
    have hk := hRC' k (Subgroup.mem_inf.mpr ⟨hkN, hkK⟩)
    have hx' : x = c * j' * k * e := by
      have : x = c * n := by simp [n]
      rw [this, hnjm]
      group
    rw [hx']
    refine mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_right hc) ?_) hk) ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hj'))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right he)
  apply le_antisymm ?_ (sup_le hJBE hCPN)
  have hBH : f5.B ≤ s.H := hBK.trans s.K_le_H
  have hEH : s.fr.E ≤ s.H := s.fr.E_le_H
  have hJH : s.J ∈ s.H := s.J_mem_H
  have hQ₀ := hirr' (P ⊓ s.H) inf_le_left
    (Sec54.mem_normalizer_inf hJN (Sec54.mem_normalizer_centralizer_singleton hJH))
    (fun b hb => Sec54.mem_normalizer_inf (hBN hb)
      (Sec54.mem_normalizer_centralizer_singleton (hBH hb)))
    (fun e he => Sec54.mem_normalizer_inf (hEN he)
      (Sec54.mem_normalizer_centralizer_singleton (hEH he)))
  rcases hQ₀ with hQ₀ | hQ₀
  ·
    have hinv : ∀ y ∈ P, s.J * y * s.J⁻¹ = y⁻¹ := by
      intro y hy
      have hyJ : s.J * y * s.J⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hJN y).mp hy
      set z := y * (s.J * y * s.J⁻¹)
      have hz : z ∈ P ⊓ s.H := by
        refine Subgroup.mem_inf.mpr ⟨P.mul_mem hy hyJ, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hJinv : s.J⁻¹ = s.J := s.J_inv
        have hc := hPab y hy _ hyJ
        calc z * s.J = ((s.J * y * s.J⁻¹) * y) * s.J := by
              simp only [z]
              rw [hc]
          _ = s.J * y * s.J⁻¹ * y * s.J := by group
          _ = s.J * y * s.J * y * s.J⁻¹ := by rw [hJinv]
          _ = s.J * z := by simp only [z]; group
      rw [hQ₀, Subgroup.mem_bot] at hz
      calc s.J * y * s.J⁻¹ = y⁻¹ * z := by simp only [z]; group
        _ = y⁻¹ := by rw [hz, mul_one]
    have hB1 : ∀ W : Subgroup G, W ≤ NP → s.J ∈ W → IsPGroup 2 W →
        W ≤ Subgroup.zpowers s.J := by
      intro W hWN hJW hW w hw
      by_contra hwJ
      have hWab := s.toHyp.isMulCommutative_of_isPGroup hW
      have hwJc : Commute s.J w :=
        congrArg Subtype.val (hWab.is_comm.comm ⟨s.J, hJW⟩ ⟨w, hw⟩)
      have hww : w * w = 1 := s.fr.mul_self_of_isPGroup (hW.to_le (Subgroup.zpowers_le.mpr hw))
      have hw1 : w ≠ 1 := fun h => hwJ (h ▸ Subgroup.one_mem _)
      have how : orderOf w = 2 := by
        have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hww])
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hw1
        · exact h
      have hwneJ : w ≠ s.J := fun h => hwJ (h ▸ Subgroup.mem_zpowers _)
      have hVN : denominatorFourGroup s.J w ≤ Subgroup.normalizer (P : Set G) := by
        rw [denominatorFourGroup_eq]
        exact sup_le (Subgroup.zpowers_le.mpr hJN) (Subgroup.zpowers_le.mpr (hWN hw))
      have hgen := four_group_odd_centralizer_generation P s.J w s.orderOf_J how hwJc hwneJ.symm
        hPodd hVN
      apply hP1
      rw [hgen]
      have hJJ : s.J * s.J = 1 := s.J_mul_J
      have hreal : ∀ u : G, orderOf u = 2 → s.J ∈ Subgroup.centralizer ({u} : Set G) →
          P ⊓ Subgroup.centralizer ({u} : Set G) = ⊥ := by
        intro u hu hJu
        rw [eq_bot_iff]
        intro y hy
        obtain ⟨hyP, hyu⟩ := Subgroup.mem_inf.mp hy
        by_contra hy1
        exact s.no_real_three h22 hp hu hyu hJu hy1 (hP3el y hyP) hJJ (hinv y hyP)
      have hJw : (s.J * w) * (s.J * w) = 1 := by
        calc s.J * w * (s.J * w) = s.J * (w * s.J) * w := by group
          _ = s.J * (s.J * w) * w := by rw [hwJc.eq]
          _ = (s.J * s.J) * (w * w) := by group
          _ = 1 := by rw [hJJ, hww, one_mul]
      have hoJw : orderOf (s.J * w) = 2 := by
        have hdvd : orderOf (s.J * w) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hJw])
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exfalso
          apply hwneJ
          have h1 := orderOf_eq_one_iff.mp h
          calc w = s.J⁻¹ * (s.J * w) := by group
            _ = s.J := by rw [h1, mul_one, s.J_inv]
        · exact h
      have h1 := hreal w how (Subgroup.mem_centralizer_singleton_iff.mpr hwJc.eq)
      have h2 := hreal (s.J * w) hoJw (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc s.J * (s.J * w) = s.J * (w * s.J) := by rw [hwJc.eq]
          _ = s.J * w * s.J := by group))
      have h0 : P ⊓ Subgroup.centralizer ({s.J} : Set G) = ⊥ := hQ₀
      rw [h0, h1, h2, sup_bot_eq, sup_bot_eq]
    have hD : ∀ W : Subgroup G, W ≤ D → IsPGroup 2 W → Nat.card W ≤ 2 := by
      intro W hWD hW
      exact Sec54.card_le_two hJN s.orderOf_J hB1 W (hWD.trans (sup_le hCPN
        (Subgroup.zpowers_le.mpr hJN))) hW
    have hxD : ∀ x ∈ NP, x * s.J * x⁻¹ ∈ D := by
      intro x hx
      have hc : x * s.J * x⁻¹ * s.J⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : x⁻¹ * y * x ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp (NP.inv_mem hx) y).mp hy
          simpa using this
        have h1 := hinv _ hy
        have h2 := hinv _ hy'
        have hJ' : s.J⁻¹ * y * s.J = y⁻¹ := by
          have := h1
          rw [s.J_inv] at this ⊢
          exact this
        have e1 : (x * s.J * x⁻¹ * s.J⁻¹) * y * (x * s.J * x⁻¹ * s.J⁻¹)⁻¹ = y := by
          calc (x * s.J * x⁻¹ * s.J⁻¹) * y * (x * s.J * x⁻¹ * s.J⁻¹)⁻¹
              = x * s.J * (x⁻¹ * (s.J⁻¹ * y * s.J) * x) * s.J⁻¹ * x⁻¹ := by group
            _ = x * s.J * (x⁻¹ * y * x)⁻¹ * s.J⁻¹ * x⁻¹ := by rw [hJ']; group
            _ = x * (s.J * (x⁻¹ * y * x) * s.J⁻¹)⁻¹ * x⁻¹ := by group
            _ = y := by rw [h2]; group
        calc y * (x * s.J * x⁻¹ * s.J⁻¹) = ((x * s.J * x⁻¹ * s.J⁻¹) * y *
              (x * s.J * x⁻¹ * s.J⁻¹)⁻¹) * (x * s.J * x⁻¹ * s.J⁻¹) := by rw [e1]
          _ = (x * s.J * x⁻¹ * s.J⁻¹) * y := by group
      have : x * s.J * x⁻¹ = (x * s.J * x⁻¹ * s.J⁻¹) * s.J := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_left hc) hJD
    have hNKodd : Odd (Nat.card (NP ⊓ s.K : Subgroup G)) := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro h2
      obtain ⟨⟨m, hm⟩, hom⟩ := exists_prime_orderOf_dvd_card' (G := (NP ⊓ s.K : Subgroup G)) 2 h2
      rw [Subgroup.orderOf_mk] at hom
      obtain ⟨hmN, hmK⟩ := Subgroup.mem_inf.mp hm
      have hmJ : Commute s.J m := (s.commute_J (s.K_le_H hmK)).symm
      have hmneJ : m ≠ s.J := fun h => s.J_not_mem_K (h ▸ hmK)
      obtain ⟨-, hVcard, -⟩ := commuting_distinct_involutions_four_group s.orderOf_J hom hmJ hmneJ
      have hle := hB1 (Subgroup.zpowers s.J ⊔ Subgroup.zpowers m)
        (sup_le (Subgroup.zpowers_le.mpr hJN) (Subgroup.zpowers_le.mpr hmN))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num))
      have := Subgroup.card_le_of_le hle
      rw [hVcard, Nat.card_zpowers, s.orderOf_J] at this
      omega
    exact key hD hxD (f5.le_of_odd hp hB₁ inf_le_right
      (le_inf hBN hBK) hNKodd)
  ·
    have hPH : P ≤ s.H := fun y hy => by
      have : y ∈ P ⊓ s.H := by rw [hQ₀]; exact hy
      exact (Subgroup.mem_inf.mp this).2
    have hJC : s.J ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hPH hy)
    have hPKE : P ≤ s.K ⊔ s.fr.E := fun y hy =>
      s.fr.mem_KE_of_odd (hPH hy) (Odd.of_dvd_nat hPodd (Subgroup.orderOf_dvd_natCard P hy))
    have hKN : ∀ x ∈ s.K ⊔ s.fr.E, x ∈ Subgroup.normalizer (s.K : Set G) :=
      fun x hx => sup_le Subgroup.le_normalizer s.fr.E_le_normalizer_K hx
    have hQ₁ := hirr' (P ⊓ s.K) inf_le_left
      (Sec54.mem_normalizer_inf hJN (s.H_le_normalizer hJH))
      (fun b hb => Sec54.mem_normalizer_inf (hBN hb) (Subgroup.le_normalizer (hBK hb)))
      (fun e he => Sec54.mem_normalizer_inf (hEN he) (s.fr.E_le_normalizer_K he))
    rcases hQ₁ with hQ₁ | hQ₁
    ·
      exfalso
      have hBC : ∀ b ∈ f5.B, ∀ y ∈ P, b * y = y * b := by
        intro b hb y hy
        have h1 : b * y * b⁻¹ * y⁻¹ ∈ P ⊓ s.K := by
          refine Subgroup.mem_inf.mpr ⟨P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBN hb) y).mp
            hy) (P.inv_mem hy), ?_⟩
          have : y * b⁻¹ * y⁻¹ ∈ s.K :=
            (Subgroup.mem_normalizer_iff.mp (hKN y (hPKE hy)) b⁻¹).mp (s.K.inv_mem (hBK hb))
          rw [show b * y * b⁻¹ * y⁻¹ = b * (y * b⁻¹ * y⁻¹) by group]
          exact s.K.mul_mem (hBK hb) this
        rw [hQ₁, Subgroup.mem_bot] at h1
        calc b * y = (b * y * b⁻¹ * y⁻¹) * (y * b) := by group
          _ = y * b := by rw [h1, one_mul]
      by_cases hPE : P ⊓ s.fr.E = ⊥
      ·
        have hBc := f5.card_B
        have hq := s.three_lt_q
        obtain ⟨b₀, hb₀, hb₀1⟩ := (Subgroup.bot_or_exists_ne_one f5.B).resolve_left (by
          intro h
          rw [h, Subgroup.card_bot] at hBc
          have h4 := s.q_mod_four hp
          omega)
        have := f5.B_cyclic
        obtain ⟨β, hβ⟩ := IsCyclic.exists_generator (α := f5.B)
        have hEb : s.fr.E ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
          intro e he
          have hpow : ∀ e ∈ s.fr.E, ∃ k : ℤ, e * b₀ * e⁻¹ = b₀ ^ k := by
            intro e he
            have heβ : e * (β : G) * e⁻¹ ∈ f5.B :=
              (Subgroup.mem_normalizer_iff.mp (f5.E_le_normalizer_B he) β).mp β.2
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hβ ⟨_, heβ⟩)
            obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hβ ⟨b₀, hb₀⟩)
            refine ⟨k, ?_⟩
            have hk' : (β : G) ^ k = e * (β : G) * e⁻¹ := by
              have := congrArg Subtype.val hk
              simpa using this
            have hi' : (β : G) ^ i = b₀ := by
              have := congrArg Subtype.val hi
              simpa using this
            rw [← hi', ← conj_zpow, ← hk', ← zpow_mul, ← zpow_mul, mul_comm]
          apply Sec53.mem_normalizer_of_conj_le
          intro y hy
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          obtain ⟨k, hk⟩ := hpow e he
          rw [← conj_zpow, hk, ← zpow_mul]
          exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
        have hPb : P ≤ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
          intro y hy
          apply Sec53.mem_normalizer_of_conj_le
          intro z hz
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          rw [← conj_zpow, show y * b₀ * y⁻¹ = b₀ by
            rw [← hBC b₀ hb₀ y hy, mul_inv_cancel_right]]
          exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
        have h53 := lemma_5_3_of h22 G s hp f5 hb₀ hb₀1
        have hcard := Sec54.card_sup_eq_mul hEN hPE
        have hdvd : Nat.card (P ⊔ s.fr.E : Subgroup G) ∣
            Nat.card (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) :=
          Subgroup.card_dvd_of_le (sup_le hPb hEb)
        rw [hcard] at hdvd
        have hNpos : Nat.card (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) ≠ 0 :=
          Nat.card_pos.ne'
        have hfac := (Nat.factorization_le_iff_dvd (Nat.mul_ne_zero Nat.card_pos.ne'
          Nat.card_pos.ne') hNpos).mpr hdvd 3
        rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
        simp only [Finsupp.add_apply] at hfac
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hk
          exact hP1 (Subgroup.eq_bot_of_card_eq P hk)
        rw [hk, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at hfac
        omega
      ·
        have hQ₂ := hirr' (P ⊓ s.fr.E) inf_le_left
          (Sec54.mem_normalizer_inf hJN (Sec53.mem_normalizer_of_conj_le fun e he => by
            rw [show s.J * e * s.J⁻¹ = e by
              rw [← Subgroup.mem_centralizer_singleton_iff.mp (hEH he), mul_inv_cancel_right]]
            exact he))
          (fun b hb => Sec53.mem_normalizer_of_conj_le fun y hy => by
            obtain ⟨hyP, -⟩ := Subgroup.mem_inf.mp hy
            rw [show b * y * b⁻¹ = y by rw [hBC b hb y hyP, mul_inv_cancel_right]]
            exact hy)
          (fun e he => Sec54.mem_normalizer_inf (hEN he) (Subgroup.le_normalizer he))
        have hPE' : P ≤ s.fr.E := by
          rcases hQ₂ with h | h
          · exact absurd h hPE
          · rw [← h]; exact inf_le_right
        have hP₁ : f5.P₁ = img s g (unip _) := hP₁g
        have hP₁N : P ≤ Subgroup.normalizer (f5.P₁ : Set G) :=
          hPE'.trans (fun e he => f5.B_le_normalizer (Subgroup.mem_sup_right he))
        have hP₁3 : IsPGroup 3 f5.P₁ := by
          apply IsPGroup.of_card (n := s.f)
          rw [f5.card_P₁, Hyp.q, hp]
        have hP₁1 : f5.P₁ ≠ ⊥ := by
          intro h
          have := f5.card_P₁
          rw [h, Subgroup.card_bot] at this
          have := s.three_lt_q
          omega
        obtain ⟨y, hyP₁, hy1, hyP⟩ := exists_fixed_ne_one hP3 hP₁3 hP₁1 hP₁N
        have hirr₁ := f5.irred hB₁ (V := f5.P₁ ⊓ Subgroup.centralizer (P : Set G))
          (by rw [← hP₁]; exact inf_le_left)
          (fun b hb v hv => (Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_inf
            (f5.B_le_normalizer (Subgroup.mem_sup_left hb))
            (Sec54.mem_normalizer_centralizer (hBN hb))) v).mp hv)
        have hP₁C : f5.P₁ ≤ Subgroup.centralizer (P : Set G) := by
          rcases hirr₁ with h | h
          · exfalso
            have : y ∈ f5.P₁ ⊓ Subgroup.centralizer (P : Set G) := Subgroup.mem_inf.mpr
              ⟨hyP₁, Subgroup.mem_centralizer_iff.mpr fun e he => by
                have := hyP e he
                calc e * y = e * y * e⁻¹ * e := by group
                  _ = y * e := by rw [this]⟩
            rw [h, Subgroup.mem_bot] at this
            exact hy1 this
          · intro z hz
            have : z ∈ f5.P₁ ⊓ Subgroup.centralizer (P : Set G) := by
              rw [h, ← hP₁]; exact hz
            exact (Subgroup.mem_inf.mp this).2
        obtain ⟨hediv, ⟨eKX⟩, -⟩ := h26i G s.toHyp s.fr hPE' hP1
        have heX : s.eX P = Nat.card P := by
          rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]
        rw [heX] at hediv
        set f'' := s.f / s.eX P with hf''
        have hf''eq : f'' = s.f / Nat.card P := by rw [hf'', heX]
        have hP₁KX : f5.P₁ ≤ s.KX P := le_inf f5.P₁_le hP₁C
        have hdvd : s.q ∣ Nat.card (s.KX P) := by
          rw [← f5.card_P₁]
          exact Subgroup.card_dvd_of_le hP₁KX
        have hcardP : 2 ≤ Nat.card P := by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP3
          rcases k with _ | k
          · rw [pow_zero] at hk
            exact absurd (Subgroup.eq_bot_of_card_eq P hk) hP1
          · rw [hk]
            calc 2 ≤ 3 := by norm_num
              _ ≤ 3 ^ (k + 1) := Nat.le_self_pow (by omega) 3
        have hf'pos : 0 < f'' := by
          rw [hf''eq]
          exact Nat.div_pos (Nat.le_of_dvd s.f_pos hediv) (by omega)
        have hf'lt : f'' < s.f := by
          rw [hf''eq]
          exact Nat.div_lt_self s.f_pos (by omega)
        have hcardF : Nat.card (GaloisField s.p f'') = s.p ^ f'' :=
          GaloisField.card s.p f'' hf'pos.ne'
        rw [Nat.card_congr eKX.toEquiv, psl2_card_formula _ ⟨s.p, f'', Fact.out, s.odd_p,
          hf'pos, hcardF⟩, hcardF] at hdvd
        set f' := f''
        rw [Hyp.q, hp] at hdvd
        have h2 : 2 ∣ (3 ^ f') ^ 2 - 1 := by
          have : Odd ((3 ^ f') ^ 2) := Odd.pow (Odd.pow (by decide))
          obtain ⟨k, hk⟩ := this
          exact ⟨k, by omega⟩
        rw [Nat.mul_div_assoc _ h2] at hdvd
        have hcop : Nat.Coprime (3 ^ s.f) (((3 ^ f') ^ 2 - 1) / 2) := by
          apply Nat.Coprime.pow_left
          rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
          intro h3
          have h3' : 3 ∣ (3 ^ f') ^ 2 - 1 := h3.trans (Nat.div_dvd_of_dvd h2)
          have h3'' : 3 ∣ (3 ^ f') ^ 2 := by
            rw [← pow_mul]
            exact dvd_pow_self 3 (by omega)
          have hpos : 1 ≤ (3 ^ f') ^ 2 := Nat.one_le_pow _ _ (by positivity)
          have := (Nat.dvd_sub h3'' h3')
          rw [Nat.sub_sub_self hpos] at this
          norm_num at this
        have := Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)
        have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp this
        omega
    ·
      have hPK : P ≤ s.K := fun y hy => by
        have : y ∈ P ⊓ s.K := by rw [hQ₁]; exact hy
        exact (Subgroup.mem_inf.mp this).2
      have hNK := f5.normalizer_le hp hB₁ hPK hP3 hP1 hBN
      have hNK1 : ∀ m ∈ NP ⊓ s.K, m * m = 1 → m = 1 := by
        intro m hm hmm
        have hodd : ∀ h : PSL(2, GaloisField s.p s.f),
            NP ⊓ s.K ≤ img s h (unip _ ⊔ torus _) → m = 1 := by
          intro h hh
          have hmem := hh hm
          have h1 : orderOf (⟨m, hmem⟩ : img s h (unip _ ⊔ torus _)) ∣
              Nat.card (img s h (unip _ ⊔ torus _)) := orderOf_dvd_natCard _
          rw [Subgroup.orderOf_mk] at h1
          have h2 : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hmm])
          rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
          · exact orderOf_eq_one_iff.mp h3
          · rw [h3] at h1
            exact absurd (Odd.of_dvd_nat (odd_card_img_borel hp h) h1) (by decide)
        rcases hNK with h | h
        · exact hodd g h
        · exact hodd _ h
      have hDC : D = Subgroup.centralizer (P : Set G) :=
        sup_eq_left.mpr (Subgroup.zpowers_le.mpr hJC)
      have hB1 : ∀ W : Subgroup G, W ≤ D → s.J ∈ W → IsPGroup 2 W →
          W ≤ Subgroup.zpowers s.J := by
        intro W hWD hJW hW w hw
        have hWab := s.toHyp.isMulCommutative_of_isPGroup hW
        have hwJc : Commute s.J w :=
          congrArg Subtype.val (hWab.is_comm.comm ⟨s.J, hJW⟩ ⟨w, hw⟩)
        have hww : w * w = 1 := s.fr.mul_self_of_isPGroup (hW.to_le (Subgroup.zpowers_le.mpr hw))
        have hwC : w ∈ Subgroup.centralizer (P : Set G) := by rw [← hDC]; exact hWD hw
        have hwH : w ∈ s.H := Subgroup.mem_centralizer_singleton_iff.mpr hwJc.eq.symm
        obtain ⟨j, hj, m, hm, rfl⟩ := s.fr.exists_decomp_H_JM hwH
        have hjc : ∀ y ∈ s.K ⊔ s.fr.E, j * y = y * j := fun y hy => s.fr.commute_of_mem_KE hj hy
        have hjj : j * j = 1 := by
          rcases eq_one_or_eq_of_mem_zpowers s.orderOf_J hj with rfl | rfl
          · exact mul_one 1
          · exact s.J_mul_J
        have hmm : m * m = 1 := by
          calc m * m = (j * j)⁻¹ * (j * (j * m) * m) := by group
            _ = (j * j)⁻¹ * (j * (m * j) * m) := by rw [hjc m hm]
            _ = (j * j)⁻¹ * ((j * m) * (j * m)) := by group
            _ = 1 := by rw [hww, hjj]; group
        have hmK := s.fr.mem_K_of_mem_KE_of_mul_self hm hmm
        have hmC : m ∈ Subgroup.centralizer (P : Set G) := by
          have h1 : m = j⁻¹ * (j * m) := by group
          rw [h1]
          exact mul_mem (inv_mem (Subgroup.zpowers_le.mpr hJC hj)) hwC
        rw [hNK1 m (Subgroup.mem_inf.mpr ⟨hCPN hmC, hmK⟩) hmm, mul_one]
        exact hj
      have hD : ∀ W : Subgroup G, W ≤ D → IsPGroup 2 W → Nat.card W ≤ 2 :=
        Sec54.card_le_two hJD s.orderOf_J hB1
      have hxD : ∀ x ∈ NP, x * s.J * x⁻¹ ∈ D := fun x hx => Subgroup.mem_sup_left
        ((Subgroup.mem_normalizer_iff.mp (Sec54.mem_normalizer_centralizer hx) s.J).mp hJC)
      exact key hD hxD hNK

end CFSG.Walter.W67
