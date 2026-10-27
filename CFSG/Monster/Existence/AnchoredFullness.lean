module

public import CFSG.Monster.Existence.AnchoredBender
public import CFSG.Monster.Existence.Principle

public section

namespace CFSG.Monster.Existence

section SylowControl

variable {E : Type*} [Group E] [Finite E]

theorem maximal_of_normalizer_le {H T : Subgroup E} (_hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hmax : ∀ P : Subgroup E, IsPGroup 2 P → T ≤ P → P ≤ H → P = T)
    (hN : Subgroup.normalizer (T : Set E) ≤ H) :
    ∀ P : Subgroup E, IsPGroup 2 P → T ≤ P → P = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P hP hTP
  by_contra hne
  have hlt : T.subgroupOf P < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hne (le_antisymm ?_ hTP)
    intro y hy
    have : (⟨y, hy⟩ : P) ∈ T.subgroupOf P := h ▸ Subgroup.mem_top _
    exact this
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨⟨n, hnP⟩, hnN, hnT⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hnT' : n ∉ T := fun h => hnT h
  have hnNE : n ∈ Subgroup.normalizer (T : Set E) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      have htP : t ∈ P := hTP ht
      have := (Subgroup.mem_normalizer_iff.1 hnN ⟨t, htP⟩).1 ht
      exact this
    · intro ht
      have htP : t ∈ P := by
        have := P.mul_mem (P.mul_mem (P.inv_mem hnP) (hTP ht)) hnP
        simpa [mul_assoc] using this
      have := (Subgroup.mem_normalizer_iff.1 hnN ⟨t, htP⟩).2 ht
      exact this
  have hnH : n ∈ H := hN hnNE
  set Q := T ⊔ Subgroup.zpowers n with hQ
  have hQP : Q ≤ P := sup_le hTP ((Subgroup.zpowers_le).2 hnP)
  have hQp : IsPGroup 2 Q := hP.to_le hQP
  have hQH : Q ≤ H := sup_le hTH ((Subgroup.zpowers_le).2 hnH)
  have hQT := hmax Q hQp le_sup_left hQH
  exact hnT' (hQT ▸ (le_sup_right : Subgroup.zpowers n ≤ Q) (Subgroup.mem_zpowers n))

end SylowControl

section Principle

variable {A : Type*} [Group A]

theorem mem_of_isConj_of_conj_mem {G : Subgroup A} {x : A}
    (hC : Subgroup.centralizer {x} ≤ G)
    (hcensus : ∀ y ∈ G, IsConj x y → ∃ g ∈ G, g * x * g⁻¹ = y)
    {y a : A} (hy : IsConj x y) (hyG : y ∈ G) (haG : a * y * a⁻¹ ∈ G) : a ∈ G := by
  obtain ⟨g₁, hg₁, e₁⟩ := hcensus y hyG hy
  have hay : IsConj x (a * y * a⁻¹) := hy.trans (isConj_iff.2 ⟨a, rfl⟩)
  obtain ⟨g₂, hg₂, e₂⟩ := hcensus _ haG hay
  refine mem_of_conj_eq hC hg₁ hg₂ ?_
  rw [e₁, e₂]

end Principle

section Fullness

variable {A : Type} [Group A] [Finite A]

theorem centralizer_le_of_anchored
    (G : Subgroup A) (x : A) (hxx : x * x = 1)
    (hC : Subgroup.centralizer {x} ≤ G)
    (hcensus : ∀ y ∈ G, IsConj x y → ∃ g ∈ G, g * x * g⁻¹ = y)
    (F : Subgroup A) (hFG : F ≤ G) (hFc : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hxK : x ∈ Subgroup.centralizer (F : Set A)) (hxF : x ∉ F)
    (hx1 : ∀ f ∈ F, IsConj x (x * f) → f = 1)
    (R : Subgroup A) (hRx : R ≤ Subgroup.centralizer {x})
    (hRK : R ≤ Subgroup.centralizer (F : Set A)) (hR2 : IsPGroup 2 R)
    (hRn : ∀ h ∈ Subgroup.centralizer (F : Set A) ⊓ Subgroup.centralizer {x}, ∀ r ∈ R,
      h * r * h⁻¹ ∈ R)
    (hCR : ∀ h ∈ Subgroup.centralizer (F : Set A) ⊓ Subgroup.centralizer {x},
      (∀ r ∈ R, h * r * h⁻¹ * r⁻¹ ∈ F) → h ∈ R)
    (hZR : ∀ r ∈ R, (∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ F) → r ∈ F ∨ x⁻¹ * r ∈ F)
    (hinv : ∃ r ∈ R, r * r ∈ F ∧ r ∉ F ∧ x⁻¹ * r ∉ F)
    (hanch : ∀ k ∈ Subgroup.centralizer (F : Set A) ⊓ Subgroup.centralizer {x},
      k * k ∈ F → k ∉ F → ∃ f ∈ F, IsConj x (k * f)) :
    Subgroup.centralizer (F : Set A) ≤ G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer (F : Set A) with hK
  have hFK : F ≤ K := fun f hf => Subgroup.mem_centralizer_iff.2 fun b hb => hFc b hb f hf
  have hcomm : ∀ k ∈ K, ∀ f ∈ F, k * f = f * k := fun k hk f hf =>
    ((Subgroup.mem_centralizer_iff.1 hk) f hf).symm
  set F' : Subgroup K := F.subgroupOf K with hF'
  have hF'n : F'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have : ((g * n * g⁻¹ : K) : A) = n := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcomm g g.2 n hn, mul_inv_cancel_right]
    rw [this]
    exact hn⟩
  set π : K →* K ⧸ F' := QuotientGroup.mk' F' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective F'
  have hπeq : ∀ a b : K, π a = π b ↔ ((a : A))⁻¹ * (b : A) ∈ F := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp
  have hπone : ∀ a : K, π a = 1 ↔ (a : A) ∈ F := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set E := K ⧸ F' with hE
  set Hs : Subgroup K := (Subgroup.centralizer {x}).subgroupOf K with hHs
  set H' : Subgroup E := Hs.map π with hH'
  set R' : Subgroup E := (R.subgroupOf K).map π with hR'
  set M : Subgroup E := (G.subgroupOf K).map π with hM
  set xK : K := ⟨x, hxK⟩ with hxKdef
  set xb : E := π xK with hxb
  have hxb1 : xb ≠ 1 := by
    rw [hxb, Ne, hπone]
    exact hxF
  have hxb2 : xb * xb = 1 := by
    rw [hxb, ← map_mul, hπone]
    change x * x ∈ F
    rw [hxx]
    exact F.one_mem
  have hxbo : orderOf xb = 2 := orderOf_eq_prime (by rw [sq, hxb2]) hxb1
  have hHsx : ∀ h : K, h ∈ Hs ↔ (h : A) * x = x * h := fun h => by
    rw [hHs, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have hxbc : ∀ y ∈ H', y * xb = xb * y := by
    rintro _ ⟨h, hh, rfl⟩
    rw [hxb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((hHsx h).1 hh)
  have hxbH : xb ∈ H' := ⟨xK, (hHsx xK).2 rfl, rfl⟩
  have hHM : H' ≤ M := Subgroup.map_mono fun h hh => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    exact hC hh
  have hR'H : R' ≤ H' := Subgroup.map_mono fun r hr => by
    rw [Subgroup.mem_subgroupOf] at hr ⊢
    exact hRx hr
  have hR'p : IsPGroup 2 R' := by
    refine IsPGroup.map ?_ π
    exact hR2.comap_of_injective K.subtype Subtype.coe_injective
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 H') := inferInstance
  set T₀ : Subgroup E := (S₀ : Subgroup H').map H'.subtype with hT₀
  have hT₀p : IsPGroup 2 T₀ := S₀.isPGroup'.map _
  have hT₀H : T₀ ≤ H' := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hT₀max : ∀ P : Subgroup E, IsPGroup 2 P → T₀ ≤ P → P ≤ H' → P = T₀ := by
    intro P hP hTP hPH
    have h1 : IsPGroup 2 (P.subgroupOf H') :=
      hP.comap_of_injective H'.subtype Subtype.coe_injective
    have h2 : (S₀ : Subgroup H') ≤ P.subgroupOf H' := fun y hy => by
      rw [Subgroup.mem_subgroupOf]
      exact hTP ⟨y, hy, rfl⟩
    have h3 := S₀.is_maximal' h1 h2
    rw [hT₀, ← h3, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPH]
  have hR'T : R' ≤ T₀ := by
    have hnorm : T₀ ≤ Subgroup.normalizer (R' : Set E) := by
      intro t ht
      obtain ⟨h, hh, rfl⟩ := hT₀H ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨r, hr, rfl⟩
        refine ⟨h * r * h⁻¹, ?_, by simp [map_mul, map_inv]⟩
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hRn h ⟨h.2, hh⟩ r hr
      · intro hy
        obtain ⟨r, hr, hr'⟩ := hy
        refine ⟨h⁻¹ * r * h, ?_, ?_⟩
        · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
          rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          have := hRn h⁻¹ ⟨(h⁻¹).2, ?_⟩ r hr
          · simpa using this
          · show (h : A)⁻¹ ∈ Subgroup.centralizer {x}
            rw [Subgroup.mem_centralizer_singleton_iff]
            have hx' := (hHsx h).1 hh
            have : (h : A)⁻¹ * x = x * (h : A)⁻¹ := by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx', mul_assoc, mul_inv_cancel,
                mul_one]
            simpa using this
        · rw [map_mul, map_mul, map_inv, hr']
          group
    have hsup := IsPGroup.to_sup_of_normal_right' hT₀p hR'p hnorm
    have := hT₀max (T₀ ⊔ R') hsup le_sup_left (sup_le hT₀H hR'H)
    exact this ▸ le_sup_right
  have hxbT : xb ∈ T₀ := by
    have hnorm : T₀ ≤ Subgroup.normalizer ((Subgroup.zpowers xb : Subgroup E) : Set E) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      have hc := hxbc t (hT₀H ht)
      intro y
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨k, ?_⟩
        simp only
        rw [(Commute.zpow_right (show Commute t xb from hc) k).eq, mul_inv_cancel_right]
      · rintro ⟨k, hk⟩
        refine ⟨k, ?_⟩
        simp only at hk ⊢
        have : t * xb ^ k * t⁻¹ = xb ^ k := by
          rw [(Commute.zpow_right (show Commute t xb from hc) k).eq, mul_inv_cancel_right]
        rw [← this] at hk
        exact mul_left_cancel (mul_right_cancel hk)
    have hzp : IsPGroup 2 (Subgroup.zpowers xb) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hxbo, pow_one]
    have hsup := IsPGroup.to_sup_of_normal_right' hT₀p hzp hnorm
    have hle : Subgroup.zpowers xb ≤ H' := (Subgroup.zpowers_le).2 hxbH
    have := hT₀max (T₀ ⊔ Subgroup.zpowers xb) hsup le_sup_left (sup_le hT₀H hle)
    exact this ▸ (le_sup_right : Subgroup.zpowers xb ≤ T₀ ⊔ Subgroup.zpowers xb)
      (Subgroup.mem_zpowers xb)
  have hcenter : ∀ y ∈ T₀, (∀ t ∈ T₀, y * t = t * y) → y = 1 ∨ y = xb := by
    intro y hy hyc
    obtain ⟨h, hh, rfl⟩ := hT₀H hy
    have hcr : ∀ r ∈ R, (h : A) * r * (h : A)⁻¹ * r⁻¹ ∈ F := by
      intro r hr
      have hrK : r ∈ K := hRK hr
      have hrT : π ⟨r, hrK⟩ ∈ T₀ := hR'T ⟨⟨r, hrK⟩, hr, rfl⟩
      have := hyc _ hrT
      have h' : π (h * ⟨r, hrK⟩ * h⁻¹ * (⟨r, hrK⟩ : K)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, this]
        group
      rw [hπone] at h'
      simpa using h'
    have hhR : (h : A) ∈ R :=
      hCR h ⟨h.2, (Subgroup.mem_centralizer_singleton_iff).2 ((hHsx h).1 hh)⟩ hcr
    rcases hZR h hhR hcr with hF | hF
    · left
      exact (hπone h).2 hF
    · right
      rw [hxb, hπeq]
      have : (x : A)⁻¹ * (h : A) ∈ F := hF
      have hinv' := F.inv_mem this
      simpa [mul_inv_rev] using hinv'
  have hNT : Subgroup.normalizer (T₀ : Set E) ≤ H' := by
    intro n hn
    obtain ⟨c, rfl⟩ := hπs n
    have hconj : π c * xb * (π c)⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.1 hn xb).1 hxbT
    have hcent : ∀ t ∈ T₀, π c * xb * (π c)⁻¹ * t = t * (π c * xb * (π c)⁻¹) := by
      intro t ht
      have ht' : (π c)⁻¹ * t * π c ∈ T₀ := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) t).1 ht
        rwa [inv_inv] at this
      have hc := hcenter xb hxbT (fun t' ht'' => ?_)
      · have hxt : xb * ((π c)⁻¹ * t * π c) = ((π c)⁻¹ * t * π c) * xb :=
          (hxbc _ (hT₀H ht')).symm
        calc π c * xb * (π c)⁻¹ * t = π c * (xb * ((π c)⁻¹ * t * π c)) * (π c)⁻¹ := by group
          _ = π c * (((π c)⁻¹ * t * π c) * xb) * (π c)⁻¹ := by rw [hxt]
          _ = t * (π c * xb * (π c)⁻¹) := by group
      · exact (hxbc t' (hT₀H ht'')).symm
    rcases hcenter _ hconj hcent with h1 | h1
    · exfalso
      apply hxb1
      have : xb = (π c)⁻¹ * (π c * xb * (π c)⁻¹) * π c := by group
      rw [this, h1]
      group
    ·
      have h2 : π (c * xK * c⁻¹) = π xK := by
        rw [map_mul, map_mul, map_inv]
        exact h1
      rw [hπeq] at h2
      set f := ((c * xK * c⁻¹ : K) : A)⁻¹ * x with hf
      have hfF : f ∈ F := h2
      have hcx : ((c * xK * c⁻¹ : K) : A) = x * f⁻¹ := by
        rw [hf]
        group
      have hfinv : f⁻¹ = 1 := by
        refine hx1 f⁻¹ (F.inv_mem hfF) ?_
        rw [← hcx]
        exact isConj_iff.2 ⟨c, rfl⟩
      have hcx' : (c : A) * x * (c : A)⁻¹ = x := by
        have := hcx
        rw [hfinv, mul_one] at this
        simpa using this
      refine ⟨c, (hHsx c).2 ?_, rfl⟩
      calc (c : A) * x = (c : A) * x * (c : A)⁻¹ * c := by group
        _ = x * c := by rw [hcx']
  have hT₀Sylow := maximal_of_normalizer_le hT₀p hT₀H hT₀max hNT
  let T : Sylow 2 E := ⟨T₀, hT₀p, fun hQ hle => hT₀Sylow _ hQ hle⟩
  have hlift : ∀ e : E, orderOf e = 2 → ∃ y : K, π y = e ∧ IsConj x (y : A) := by
    intro e he
    have hzp : IsPGroup 2 (Subgroup.zpowers e) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, he, pow_one]
    obtain ⟨S, hS⟩ := hzp.exists_le_sylow
    obtain ⟨d, hd⟩ := MulAction.exists_smul_eq E T S
    have heS : e ∈ (S : Subgroup E) := hS (Subgroup.mem_zpowers e)
    rw [← hd, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at heS
    have heT : d⁻¹ * e * d ∈ T₀ := by
      simpa [MulAut.smul_def, MulAut.conj_apply] using heS
    obtain ⟨k, hkH, hk⟩ := hT₀H heT
    have hk2 : (k : A) * k ∈ F := by
      have h1 : π (k * k) = 1 := by
        rw [map_mul, hk]
        have : e * e = 1 := by rw [← sq, ← he, pow_orderOf_eq_one]
        calc d⁻¹ * e * d * (d⁻¹ * e * d) = d⁻¹ * (e * e) * d := by group
          _ = 1 := by rw [this]; group
      exact (hπone (k * k)).1 h1
    have hk1 : (k : A) ∉ F := by
      rw [← hπone k, hk]
      intro h
      have : e = 1 := by
        have h' : e = d * (d⁻¹ * e * d) * d⁻¹ := by group
        rw [h', h]
        group
      rw [this, orderOf_one] at he
      norm_num at he
    obtain ⟨f, hf, hfc⟩ := hanch k ⟨k.2, (Subgroup.mem_centralizer_singleton_iff).2
      ((hHsx k).1 hkH)⟩ hk2 hk1
    obtain ⟨c, rfl⟩ := hπs d
    refine ⟨c * (k * ⟨f, hFK hf⟩) * c⁻¹, ?_, ?_⟩
    · have hf1 : π ⟨f, hFK hf⟩ = 1 := (hπone _).2 hf
      rw [map_mul, map_mul, map_mul, map_inv, hf1, mul_one, hk]
      group
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hfc.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hanchM : ∀ i ∈ M, orderOf i = 2 → ∀ g : E, g * i * g⁻¹ ∈ M → g ∈ M := by
    intro i hiM hi g hg
    obtain ⟨y, hy, hyx⟩ := hlift i hi
    obtain ⟨m, hm, hmi⟩ := hiM
    have hyG : (y : A) ∈ G := by
      have h1 : π m = π y := hmi.trans hy.symm
      rw [hπeq] at h1
      have hm' : (m : A) ∈ G := hm
      have := G.mul_mem hm' (hFG h1)
      simpa using this
    obtain ⟨c, rfl⟩ := hπs g
    obtain ⟨m', hm', hm'i⟩ := hg
    have hcyG : (c : A) * y * (c : A)⁻¹ ∈ G := by
      have h1 : π m' = π (c * y * c⁻¹) := by
        rw [hm'i, map_mul, map_mul, map_inv, hy]
      rw [hπeq] at h1
      have hm'' : (m' : A) ∈ G := hm'
      have := G.mul_mem hm'' (hFG h1)
      simpa using this
    have hcG := mem_of_isConj_of_conj_mem hC hcensus hyx hyG hcyG
    exact ⟨c, hcG, rfl⟩
  have hZ : Nat.card (Subgroup.center T) = 2 := by
    have hz : Subgroup.center (T : Subgroup E) = Subgroup.zpowers (⟨xb, hxbT⟩ : T₀) := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_center_iff] at hy
        rcases hcenter y y.2 (fun t ht => (congrArg Subtype.val (hy ⟨t, ht⟩)).symm) with h | h
        · rw [show y = 1 from Subtype.ext h]
          exact Subgroup.one_mem _
        · rw [show y = ⟨xb, hxbT⟩ from Subtype.ext h]
          exact Subgroup.mem_zpowers _
      · rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro t
        exact Subtype.ext (hxbc t (hT₀H t.2))
    rw [hz, Nat.card_zpowers, Subgroup.orderOf_mk, hxbo]
  obtain ⟨r, hrR, hrr, hrF, hrx⟩ := hinv
  set rb : E := π ⟨r, hRK hrR⟩ with hrb
  have hrbT : rb ∈ T₀ := hR'T ⟨⟨r, hRK hrR⟩, hrR, rfl⟩
  have hrb1 : rb ≠ 1 := by
    rw [hrb, Ne, hπone]
    exact hrF
  have hrbo : orderOf rb = 2 := by
    refine orderOf_eq_prime ?_ hrb1
    rw [sq, hrb, ← map_mul, hπone]
    exact hrr
  have hne : xb ≠ rb := by
    rw [hxb, hrb, Ne, hπeq]
    exact hrx
  have hMtop := eq_top_of_anchored_involutions M hanchM T (hT₀H.trans hHM) hZ hxbT hrbT hne
    hxbo hrbo
  intro k hk
  obtain ⟨m, hm, hmk⟩ : π ⟨k, hk⟩ ∈ M := hMtop ▸ Subgroup.mem_top _
  rw [hπeq] at hmk
  have hm' : (m : A) ∈ G := hm
  have := G.mul_mem hm' (hFG hmk)
  simpa using this

end Fullness


end CFSG.Monster.Existence
