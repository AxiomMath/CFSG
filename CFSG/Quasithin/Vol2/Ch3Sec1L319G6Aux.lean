module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Hall
public import CFSG.Quasithin.Vol2.Ch3zTorus
public import CFSG.Quasithin.Vol2.Ch3zSetup

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Ch3z
open scoped Pointwise

section Lift

theorem exists_cop6_pow_eq {A B : Type*} [Group A] [Group B] (φ : A →* B) {x : A}
    (hx : IsOfFinOrder x) (hcop : Nat.Coprime (orderOf (φ x)) 6) :
    ∃ n : ℕ, Nat.Coprime (orderOf (x ^ n)) 6 ∧ φ (x ^ n) = φ x := by
  have hopos : 0 < orderOf x := hx.orderOf_pos
  obtain ⟨a, n₁, hn₁, hoa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hopos.ne' 2 (by norm_num)
  have hn₁0 : n₁ ≠ 0 := by
    rintro rfl
    simp at hoa
    omega
  obtain ⟨b, m, hm, hob⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn₁0 3 (by norm_num)
  have hm2 : ¬ 2 ∣ m := fun h2 => hn₁ (hob ▸ Dvd.dvd.mul_left h2 _)
  have hmcop : Nat.Coprime m 6 := by
    have h2 : Nat.Coprime m 2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm2 |>.symm
    have h3 : Nat.Coprime m 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm |>.symm
    exact (Nat.coprime_mul_iff_right (k := m) (m := 2) (n := 3)).mpr ⟨h2, h3⟩
  have hc2 : Nat.Coprime (2 ^ a) (orderOf (φ x)) :=
    Nat.Coprime.pow_left a (Nat.Coprime.coprime_dvd_left (by norm_num : 2 ∣ 6) hcop.symm)
  have hc3 : Nat.Coprime (3 ^ b) (orderOf (φ x)) :=
    Nat.Coprime.pow_left b (Nat.Coprime.coprime_dvd_left (by norm_num : 3 ∣ 6) hcop.symm)
  have hcu : Nat.Coprime (2 ^ a * 3 ^ b) (orderOf (φ x)) :=
    Nat.coprime_mul_iff_left.mpr ⟨hc2, hc3⟩
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, n ≡ 0 [MOD 2 ^ a * 3 ^ b] ∧ n ≡ 1 [MOD orderOf (φ x)] :=
    ⟨Nat.chineseRemainder hcu 0 1, (Nat.chineseRemainder hcu 0 1).2.1,
      (Nat.chineseRemainder hcu 0 1).2.2⟩
  refine ⟨n, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).mp hn1
    have hpow : (x ^ n) ^ m = 1 := by
      rw [← pow_mul, hc, show 2 ^ a * 3 ^ b * c * m = c * orderOf x by
        rw [hoa, hob]; ring, pow_mul', pow_orderOf_eq_one, one_pow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow) hmcop
  · have h3 : (φ x) ^ n = (φ x) ^ 1 := pow_eq_pow_iff_modEq.mpr hn2
    rw [map_pow, h3, pow_one]

end Lift

section Hall

variable {G : Type} [Group G] [Finite G]

theorem hall_centralizes {T S V : Subgroup G} (hT : IsSylowTwoOf T S) (hS : Group.IsSolvable ↥S)
    (hSV : S ≤ Subgroup.normalizer (V : Set G))
    (hF : ∀ F : Subgroup G, F ≤ S → (∀ x ∈ F, Nat.Coprime (orderOf x) 6) →
      ((F ⊔ T : Subgroup G) : Set G) = (F : Set G) * (T : Set G) →
      F ≤ Subgroup.centralizer (V : Set G)) :
    ∀ y ∈ S, Nat.Coprime (orderOf y) 6 → ∀ v ∈ V, y * v * y⁻¹ = v := by
  have hT2 : IsPGroup 2 (T.subgroupOf S) := hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  obtain ⟨F', hF'cop, hF'perm, hF'conj⟩ := exists_permutable_hall_ge5 hS hT2 hT.2.2
  let F : Subgroup G := F'.map S.subtype
  have hFS : F ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcop : ∀ x ∈ F, Nat.Coprime (orderOf x) 6 := by
    rintro _ ⟨x, hx, rfl⟩
    have := hF'cop x hx
    simpa [F, Subgroup.orderOf_coe] using this
  have hTmap : (T.subgroupOf S).map S.subtype = T := by
    rw [Subgroup.map_subgroupOf_eq_of_le hT.1]
  have hperm : ((F ⊔ T : Subgroup G) : Set G) = (F : Set G) * (T : Set G) := by
    have h1 : (F ⊔ T : Subgroup G) = (F' ⊔ T.subgroupOf S).map S.subtype := by
      rw [Subgroup.map_sup, hTmap]
    rw [h1, Subgroup.coe_map, hF'perm, Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, hTmap]
  have hFV := hF F hFS hcop hperm
  intro y hy hycop v hv
  obtain ⟨s, hs⟩ := hF'conj ⟨y, hy⟩ (by simpa [Subgroup.orderOf_mk] using hycop)
  have hsF : ((s : G) * y * (s : G)⁻¹) ∈ F := ⟨s * ⟨y, hy⟩ * s⁻¹, hs, rfl⟩
  have hsN : (s : G) ∈ Subgroup.normalizer (V : Set G) := hSV s.2
  have hw : (s : G) * v * (s : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hsN v).mp hv
  have h1 : ((s : G) * v * (s : G)⁻¹) * ((s : G) * y * (s : G)⁻¹) =
      ((s : G) * y * (s : G)⁻¹) * ((s : G) * v * (s : G)⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hFV hsF) _ hw
  have h2 : ((s : G) * y * (s : G)⁻¹) * ((s : G) * v * (s : G)⁻¹) * ((s : G) * y * (s : G)⁻¹)⁻¹ =
      (s : G) * v * (s : G)⁻¹ := by
    rw [← h1]
    group
  calc y * v * y⁻¹ = (s : G)⁻¹ * (((s : G) * y * (s : G)⁻¹) * ((s : G) * v * (s : G)⁻¹) *
        ((s : G) * y * (s : G)⁻¹)⁻¹) * (s : G) := by group
    _ = v := by rw [h2]; group

end Hall

section Chief

variable {G : Type} [Group G] [Finite G] {H T M₂ U L N : Subgroup G}

theorem isSolvable_kerIn_G6 {Γ : Type} [Group Γ] [Finite Γ] {X Tx Mx : Subgroup Γ}
    (hmin : MinParabolic X Tx Mx) : Group.IsSolvable ↥(kerIn Mx X) := by
  have h1 := hmin.subgroupOf.isSolvable_kerIn
  rw [B6.kerIn_subgroupOf_top] at h1
  have hle : kerIn Mx X ≤ X := hmin.kerIn_le_H
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.injective

theorem isSolvable_of_chief_G6 (hmp : MinParabolic H T M₂) (hUT : U ≤ T)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    (hsolv : Group.IsSolvable ↥(chiefImg (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1) M₂)) : Group.IsSolvable ↥M₂ := by
  have hHL := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    (hstep.1.1.trans (hUT.trans hmp.isSylow.1)).trans hHL
  have hM₂H : M₂ ≤ H := hmp.maximal.1.le
  let S₀ : Subgroup ↥H := M₂.subgroupOf H
  let ψS : ↥S₀ →* ↥(chiefImg hHL hHN M₂) :=
    ((chiefPsi hHL hHN).comp S₀.subtype).codRestrict (chiefImg hHL hHN M₂)
      (fun x => ⟨x.1, x.2, rfl⟩)
  have hker : ∀ x : ↥S₀, ψS x = 1 → ((x : ↥H) : G) ∈ kerIn M₂ H := by
    intro x hx
    have h1 : chiefPsi hHL hHN (x : ↥H) = 1 := congrArg Subtype.val hx
    have h2 : chiefHom hHL hHN (x : ↥H) = 1 := Subtype.ext h1
    have h3 := (chiefHom_eq_one_iff hHL hHN hNL (x : ↥H)).1 h2
    exact centralizerMod_le_kerIn hmp hUT hstep hnc h3
  haveI : Group.IsSolvable ↥(kerIn M₂ H) := isSolvable_kerIn_G6 hmp
  let g₀ : ↥ψS.ker →* G := H.subtype.comp (S₀.subtype.comp ψS.ker.subtype)
  let g : ↥ψS.ker →* ↥(kerIn M₂ H) := g₀.codRestrict (kerIn M₂ H) (fun k => hker k.1 k.2)
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 : ((a : ↥S₀) : ↥H) = ((b : ↥S₀) : ↥H) := by
      apply Subtype.ext
      have := congrArg (fun y : ↥(kerIn M₂ H) => (y : G)) hab
      exact this
    exact Subtype.ext (Subtype.ext h1)
  haveI : Group.IsSolvable ↥ψS.ker := Group.isSolvable_of_isSolvable_injective hginj
  haveI : Group.IsSolvable ↥S₀ :=
    Group.isSolvable_of_ker_le_range ψS.ker.subtype ψS (by simp)
  exact Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hM₂H).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hM₂H).surjective

end Chief

section Torus

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {𝓗 : Finset (Subgroup (MulAut V))}

theorem BlkCtx.eq_one_of_fixed_conj (h : BlkCtx X T M 𝓗) {H₀ : Subgroup (MulAut V)} (hH₀ : H₀ ∈ 𝓗)
    {d₀ : MulAut V} (hd₀ : TorusProp T H₀ d₀) {v : V} (hvT : ∀ t ∈ T, t v = v) (hvd : d₀ v = v) :
    v = 1 := by
  classical
  have hvD : ∀ t ∈ T, (t * d₀ * t⁻¹) v = v := by
    intro t ht
    have h1 : t⁻¹ v = v := by
      have := hvT t⁻¹ (T.inv_mem ht)
      exact this
    show t (d₀ (t⁻¹ v)) = v
    rw [h1, hvd]
    exact hvT t ht
  have key : ∀ 𝓕 : Finset (Subgroup (MulAut V)), 𝓕 ⊆ 𝓗 → ∀ w ∈ ⨆ H ∈ 𝓕, commV H,
      (∀ t ∈ T, t w = w) → (∀ t ∈ T, (t * d₀ * t⁻¹) w = w) → w = 1 := by
    intro 𝓕
    induction 𝓕 using Finset.induction_on with
    | empty =>
      intro _ w hw _ _
      simpa using hw
    | insert H₁ 𝓕' hH₁ ih =>
      intro hsub w hw hwT hwD
      have hH₁𝓗 : H₁ ∈ 𝓗 := hsub (Finset.mem_insert_self _ _)
      have hsub' : 𝓕' ⊆ 𝓗 := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.iSup_insert] at hw
      obtain ⟨a, ha, r, hr, rfl⟩ := Subgroup.mem_sup.mp hw
      obtain ⟨t, htT, hconj⟩ := h.trans hH₀ hH₁𝓗
      have hd₁ : TorusProp T H₁ (t * d₀ * t⁻¹) := hconj ▸ hd₀.conj htT
      have hrfix : r ∈ fixV H₁ := by
        have : (⨆ H ∈ 𝓕', commV H) ≤ fixV H₁ := by
          refine iSup₂_le fun H hH => ?_
          intro v hv x hx
          have hne : H ≠ H₁ := fun heq => hH₁ (heq ▸ hH)
          exact h.act_commV_of_ne (hsub' hH) hH₁𝓗 hne hx hv
        exact this hr
      have hfixr : ∀ x ∈ H₁, x r = r := fun x hx => hrfix x hx
      have ha1 : a = 1 := by
        refine hd₁.2.2 a ha (fun q hq => ?_) ?_
        · have h1 := hwT q hq.1
          rw [map_mul, hfixr q hq.2] at h1
          exact mul_right_cancel h1
        · have h1 := hwD t htT
          rw [map_mul, hfixr _ hd₁.1] at h1
          exact mul_right_cancel h1
      subst ha1
      rw [one_mul] at hwT hwD ⊢
      exact ih hsub' r hr hwT hwD
  refine key 𝓗 le_rfl v ?_ hvT hvD
  rw [h.iSup_comm]
  trivial

end Torus

end CFSG.Quasithin.H13.L319
