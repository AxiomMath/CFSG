module

public import CFSG.Quasithin.Background.AutOnSylow
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Avg
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Quot

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L15420

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_autOn {V P S : Subgroup G} (hSP : IsSylowTwoOf S P)
    (hP : P ≤ Subgroup.normalizer (V : Set G)) : IsSylowTwoOf (autOn S V) (autOn P V) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn hSP hP

theorem autOn_inf_centralizer_eq_bot {K R V : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (hKRV : K ⊔ R ≤ Subgroup.normalizer (V : Set G))
    (hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K)
    (hQV : pCoreOf 2 (K ⊔ R) ≤ Subgroup.centralizer (V : Set G)) :
    autOn (K ⊔ R) V ⊓ Subgroup.centralizer (autOn K V : Set (MulAut V)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := autOn K V with hLdef
  set N := Subgroup.normalizer (V : Set G) with hNdef
  have hKN : K ≤ N := le_sup_left.trans hKRV
  have hKRK : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  set P : Subgroup G := (K ⊔ R) ⊓
    ((Subgroup.centralizer (L : Set (MulAut V))).comap (conjAct V)).map N.subtype with hPdef
  have hnorm : ∀ x : N, (x : G) ∈ K ⊔ R →
      conjAct V x ∈ Subgroup.normalizer (L : Set (MulAut V)) := by
    have key : ∀ x : N, (x : G) ∈ K ⊔ R → ∀ l ∈ L, conjAct V x * l * (conjAct V x)⁻¹ ∈ L := by
      intro x hx l hl
      obtain ⟨k, hk, rfl⟩ := hl
      refine ⟨x * k * x⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hKRK hx) k).mp hk
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨key x hx l, fun h => ?_⟩
    have h1 := key x⁻¹ ((K ⊔ R).inv_mem hx) _ h
    rw [map_inv, inv_inv] at h1
    simpa [mul_assoc] using h1
  have hPn : K ⊔ R ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ h ∈ K ⊔ R, ∀ g ∈ P, h * g * h⁻¹ ∈ P := by
      intro h hh g hg
      obtain ⟨hgKR, x, hx, rfl⟩ := hg
      set hN : N := ⟨h, hKRV hh⟩ with hhNdef
      refine ⟨(K ⊔ R).mul_mem ((K ⊔ R).mul_mem hh hgKR) ((K ⊔ R).inv_mem hh),
        hN * x * hN⁻¹, ?_, rfl⟩
      change conjAct V (hN * x * hN⁻¹) ∈ Subgroup.centralizer _
      rw [map_mul, map_mul, map_inv]
      have hc := A4.mem_normalizer_centralizer (hnorm hN hh)
      exact (Subgroup.mem_normalizer_iff.mp hc _).mp hx
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key h hh g, fun hg => ?_⟩
    have := key h⁻¹ ((K ⊔ R).inv_mem hh) _ hg
    simpa [mul_assoc] using this
  have hKP : K ⊓ P ≤ pCoreOf 2 K := by
    rintro g ⟨hgK', -, x, hx, rfl⟩
    have hgK : (x : G) ∈ K := hgK'
    have hcomm : ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro k hk
      refine hCK ⟨K.mul_mem (K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK)) (K.inv_mem hk), ?_⟩
      have hkl : conjAct V ⟨k, hKN hk⟩ ∈ L := ⟨⟨k, hKN hk⟩, hk, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hx _ hkl
      have h2 : conjAct V (x * ⟨k, hKN hk⟩ * x⁻¹ * ⟨k, hKN hk⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      exact A4.conjAct_eq_one_iff.mp h2
    have hq : quotConj K (x : G) (Subgroup.le_normalizer hgK) = 1 :=
      (quotConj_eq_one_iff _).mpr hcomm
    rw [quotConj_of_mem hgK] at hq
    have hc : ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro a
      have := congrArg (fun φ => φ a) hq
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc a * ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K)
          = ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) * a *
              ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹ *
              ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by rw [this]
        _ = ((⟨(x : G), hgK⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) * a := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact mk_eq_one_iff.mp hc
  have hP2 : IsPGroup 2 P := isPGroup_of_le_sup hR hRK inf_le_left
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le hKP)
  have hPQ : P ≤ pCoreOf 2 (K ⊔ R) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hPn hP2
  rw [eq_bot_iff]
  rintro γ ⟨⟨x, hx, rfl⟩, hγ⟩
  have hxP : (x : G) ∈ P := ⟨hx, x, hγ, rfl⟩
  exact (Subgroup.mem_bot).mpr (A4.conjAct_eq_one_iff.mpr (hQV (hPQ hxP)))

theorem isQuotientOfSQTKCat_autOn {H I V : Subgroup G} (hI : CFSG.SectionRank.IsSQTKCat ↥I)
    (hHI : H ≤ I) (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    G64.IsQuotientOfSQTKCat ↥(autOn H V) := by
  let g₁ : ↥(H.subgroupOf I) →* Subgroup.normalizer (V : Set G) :=
    (I.subtype.comp (H.subgroupOf I).subtype).codRestrict _ fun y => hHV y.2
  let f : ↥(H.subgroupOf I) →* ↥(autOn H V) :=
    ((conjAct V).comp g₁).codRestrict (autOn H V) fun y => ⟨g₁ y, y.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨⟨x, hHI hx⟩, hx⟩, rfl⟩
  exact ⟨↥(H.subgroupOf I), inferInstance, inferInstance, f.ker, inferInstance,
    hI.subgroup _, ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

end L15420

namespace Comp15420

variable {G : Type} [Group G] [Finite G] {T : Subgroup G}
variable {s : Setting15419 G T} {I₀ K : Subgroup G} {y : G}

theorem mul_sq_ne {N : ℕ} (hN : N = 2520 ∨ N = 6048) (q : ℕ) : 2 * N ≠ q * (q ^ 2 - 1) := by
  intro h
  rcases Nat.lt_or_ge q 24 with hq | hq
  · interval_cases q <;> omega
  · have h1 : 24 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    have : 24 * (24 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq (Nat.sub_le_sub_right h1 1)
    norm_num at this
    omega

end Comp15420

end CFSG.Quasithin.EmptyFaithfulMultiple
