module

public import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofMax
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AltSixCentralizer
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.Native.ONTriple Subgroup

theorem mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {g : G} (hg : g ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, g = h * k := by
  let S : Subgroup G :=
    { carrier := {g | ∃ h ∈ H, ∃ k ∈ K, g = h * k}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
        refine ⟨h₁ * h₂, mul_mem hh₁ hh₂, k₁ * k₂, mul_mem hk₁ hk₂, ?_⟩
        have := hc h₂ hh₂ k₁ hk₁
        calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
          _ = h₁ * (h₂ * k₁) * k₂ := by rw [this]
          _ = h₁ * h₂ * (k₁ * k₂) := by group
      inv_mem' := by
        rintro _ ⟨h, hh, k, hk, rfl⟩
        refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
        have := hc h⁻¹ (inv_mem hh) k⁻¹ (inv_mem hk)
        rw [mul_inv_rev, this] }
  have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, one_mem _, by simp⟩)
    (fun k hk => ⟨1, one_mem _, k, hk, by simp⟩)
  exact hle hg

theorem zpow_eq_pow_fin {G : Type*} [Group G] {y : G} (hy : y ^ 3 = 1) (j : ℤ) :
    ∃ i : Fin 3, y ^ j = y ^ (i : ℕ) := by
  refine ⟨⟨(j % 3).toNat, by omega⟩, ?_⟩
  rw [zpow_eq_zpow_emod j (n := 3) (by simpa using hy), ← zpow_natCast,
    Int.toNat_of_nonneg (by omega)]

section Model


theorem core_pow_nine {A : Subgroup GM} (hA : Late.IsE27 A) (c : ℕ)
    (hx : xG 0 * zG ^ c ∈ A) : ∀ g ∈ Subgroup.centralizer (A : Set GM), g ^ 9 = 1 := by
  set x : GM := xG 0 * zG ^ c with hxdef
  have hcomm := comm_of_E27 hA
  have hx0 : xG 0 ^ 3 = 1 := xG0_cube
  have hz3 : zG ^ 3 = 1 := relG.xcube
  have hxz : Commute (xG 0) (zG ^ c) := (Commute.pow_left (zG_central (xG 0)) c).symm
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, hxz.mul_pow, hx0, ← pow_mul, mul_comm c 3, pow_mul, hz3, one_pow, one_mul]
  have hkx : ∀ k ∈ K0G, Commute x k := by
    intro k hk
    have h1 : Commute (xG 0) k := (K0_comm hk).symm
    have h2 : Commute (zG ^ c) k := Commute.pow_left (zG_central k) c
    exact h1.mul_left h2
  have hC : Subgroup.centralizer ({x} : Set GM) = zpowers x ⊔ K0G := by
    have := (centralizer_base (α := 1) (by norm_num) c).1
    simpa only [pow_one] using this
  have hdecomp : ∀ y ∈ Subgroup.centralizer ({x} : Set GM), ∃ i : ℤ, ∃ k : K0G, y = x ^ i * k := by
    intro y hy
    rw [hC] at hy
    obtain ⟨h, hh, k, hk, rfl⟩ := mem_sup_of_commute (fun h hh k hk => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((hkx k hk).zpow_left m).eq) hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ⟨m, ⟨k, hk⟩, rfl⟩
  have hAx : ∀ a ∈ A, a ∈ Subgroup.centralizer ({x} : Set GM) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx a ha).symm
  have key : ∃ a ∈ A, ∃ j : ℤ, ∃ k : K0G, a = x ^ j * k ∧ actK k ≠ 1 := by
    by_contra hno
    push Not at hno
    have hsub : (A : Set GM) ⊆ ↑(Finset.univ.image
        (fun p : Fin 3 × Fin 3 => x ^ (p.1 : ℕ) * zG ^ (p.2 : ℕ))) := by
      intro a ha
      obtain ⟨j, k, hk⟩ := hdecomp a (hAx a ha)
      have hk1 := hno a ha j k hk
      have hkz : k ∈ actK.ker := hk1
      rw [ker_actK] at hkz
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hkz
      have hkm : (k : GM) = zG ^ m := by
        rw [← hm]
        rfl
      obtain ⟨i₁, hi₁⟩ := zpow_eq_pow_fin hx3 j
      obtain ⟨i₂, hi₂⟩ := zpow_eq_pow_fin hz3 m
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨(i₁, i₂), by simp only [hk, hkm, hi₁, hi₂]⟩
    have hle : Nat.card A ≤ 9 := by
      have h1 : Nat.card A = (A : Set GM).ncard := Nat.card_coe_set_eq _
      have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at h2
      have h3 := (Finset.card_image_le (s := (Finset.univ : Finset (Fin 3 × Fin 3)))
        (f := fun p : Fin 3 × Fin 3 => x ^ (p.1 : ℕ) * zG ^ (p.2 : ℕ)))
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h3
      omega
    have := hA.2
    omega
  obtain ⟨a, haA, j, ka, hae, hτ1⟩ := key
  have hka3 : ka ^ 3 = 1 := by
    have h1 : (a : GM) ^ 3 = 1 := hA.1.2 a haA
    have h2 : Commute (x ^ j) (ka : GM) := (hkx ka ka.2).zpow_left j
    rw [hae, h2.mul_pow] at h1
    have h3 : (x ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    rw [h3, one_mul] at h1
    exact Subtype.ext h1
  have hτ3 : actK ka ^ 3 = 1 := by rw [← map_pow, hka3, map_one]
  have hsign : ∀ k : K0G, Equiv.Perm.sign (actK k) = 1 := fun k =>
    Equiv.Perm.mem_alternatingGroup.mp (range_actK ▸ ⟨k, rfl⟩)
  intro g hg
  have hgx : g ∈ Subgroup.centralizer ({x} : Set GM) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff.mp hh]
      exact (Subgroup.mem_centralizer_iff.mp hg x hx)
  obtain ⟨i, k, hgk⟩ := hdecomp g hgx
  have hga : g * a = a * g := (Subgroup.mem_centralizer_iff.mp hg a haA).symm
  have hkk : k * ka = ka * k := by
    have e1 : g * a = x ^ i * x ^ j * ((k : GM) * ka) := by
      rw [hgk, hae]
      exact Commute.mul_mul_mul_comm ((hkx k k.2).zpow_left j).symm (x ^ i) (ka : GM)
    have e2 : a * g = x ^ j * x ^ i * ((ka : GM) * k) := by
      rw [hgk, hae]
      exact Commute.mul_mul_mul_comm ((hkx ka ka.2).zpow_left i).symm (x ^ j) (k : GM)
    have hij : x ^ i * x ^ j = x ^ j * x ^ i := by
      rw [← zpow_add, ← zpow_add, add_comm]
    rw [e1, e2, hij] at hga
    exact Subtype.ext (mul_left_cancel hga)
  have hκτ : actK k * actK ka = actK ka * actK k := by rw [← map_mul, ← map_mul, hkk]
  have hκ3 : actK k ^ 3 = 1 :=
    alt_six_centralizer_cube (actK ka) hτ3 hτ1 (hsign ka) (actK k) (hsign k) hκτ
  have hk3 : (k ^ 3 : K0G) ∈ actK.ker := by
    rw [MonoidHom.mem_ker, map_pow, hκ3]
  rw [ker_actK] at hk3
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hk3
  have hk9 : ((k : GM)) ^ 9 = 1 := by
    have h1 : ((k : GM)) ^ 3 = zG ^ m := by
      have := congrArg Subtype.val hm
      simpa using this.symm
    calc (k : GM) ^ 9 = ((k : GM) ^ 3) ^ 3 := by rw [← pow_mul]
      _ = 1 := by
        rw [h1, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have hxi : (x ^ i) ^ 9 = 1 := by
    have : x ^ 9 = 1 := by
      calc x ^ 9 = (x ^ 3) ^ 3 := by rw [← pow_mul]
        _ = 1 := by rw [hx3, one_pow]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  rw [hgk, ((hkx k k.2).zpow_left i).mul_pow, hxi, hk9, one_mul]

theorem model_pow_nine
    {A : Subgroup GM} (hA : Late.IsE27 A) :
    ∀ g ∈ Subgroup.centralizer (A : Set GM), g ^ 9 = 1 := by
  have hcomm := comm_of_E27 hA
  obtain ⟨P, hP⟩ := (isPGroup_of_E27 hA).exists_le_sylow
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hAP : ∀ y ∈ A, (MulAut.conj g₀).toMonoidHom y ∈ P0G := by
    intro y hy
    rw [← P0Syl_coe, ← hg₀, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP hy)
  set A₁ : Subgroup GM := A.map (MulAut.conj g₀).toMonoidHom with hA₁
  have hA₁E : Late.IsE27 A₁ := Sec13.ON134.isE27_map hA _ (MulAut.conj g₀).injective
  have hA₁P : A₁ ≤ P0G := by
    rintro _ ⟨y, hy, rfl⟩
    exact hAP y hy
  have hzA₁ : zG ∈ A₁ := zG_mem_of_27 hA₁P (comm_of_E27 hA₁E) hA₁E.2
  obtain ⟨y₁, hy₁A, hy₁z⟩ : ∃ y ∈ A₁, y ∉ zpowers zG := by
    by_contra hno
    push Not at hno
    have hle : A₁ ≤ zpowers zG := hno
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, relG.orderOf_x] at h1
    have := hA₁E.2
    omega
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 (hA₁P hy₁A) hy₁z
  set n : GM := wordN w with hn
  set h : GM := n⁻¹ * g₀ with hh
  set A₂ : Subgroup GM := A.map (MulAut.conj h).toMonoidHom with hA₂
  have hA₂E : Late.IsE27 A₂ := Sec13.ON134.isE27_map hA _ (MulAut.conj h).injective
  have hx₂ : xG 0 * zG ^ c ∈ A₂ := by
    obtain ⟨y, hy, hyy⟩ := hy₁A
    refine ⟨y, hy, ?_⟩
    rw [← hwc, ← hyy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hh, mul_inv_rev, inv_inv]
    group
  have hcore := core_pow_nine hA₂E c hx₂
  intro g hg
  have hg' : h * g * h⁻¹ ∈ Subgroup.centralizer (A₂ : Set GM) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hg a ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc h * a * h⁻¹ * (h * g * h⁻¹) = h * (a * g) * h⁻¹ := by group
      _ = h * (g * a) * h⁻¹ := by rw [this]
      _ = h * g * h⁻¹ * (h * a * h⁻¹) := by group
  have h9 := hcore _ hg'
  have : h * g ^ 9 * h⁻¹ = 1 := by
    rw [← conj_pow]
    exact h9
  simpa using this

end Model

theorem centralizer_pow_nine_eq_one
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) : ∀ g ∈ Subgroup.centralizer (P : Set X), g ^ 9 = 1 := by
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  have hP' : Late.IsE27 (P.map ψ.toMonoidHom) :=
    Sec13.ON134.isE27_map hP ψ.toMonoidHom ψ.injective
  intro g hg
  have hg' : ψ g ∈ Subgroup.centralizer ((P.map ψ.toMonoidHom : Subgroup GM) : Set GM) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨p, hp, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hg p hp
    change ψ p * ψ g = ψ g * ψ p
    rw [← map_mul, ← map_mul, this]
  have := model_pow_nine hP' _ hg'
  apply ψ.injective
  rw [map_pow, this, map_one]

theorem isPGroup_centralizer
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P : Subgroup X}
    (hP : Late.IsE27 P) : IsPGroup 3 (Subgroup.centralizer (P : Set X)) := fun g =>
  ⟨2, Subtype.ext (centralizer_pow_nine_eq_one hperf hT hP g g.2)⟩

theorem isSolvable_inf_centralizer
    {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ} {e : Γ} (hA : Late.IsE27 A) (heA : e ∈ A)
    (he1 : e ≠ 1) (hLe : L ≤ Subgroup.centralizer ({e} : Set Γ))
    (hAL : A ≤ Subgroup.normalizer (L : Set Γ))
    (hLq : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hON3 : Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L)
      CFSG.Blueprint.NativeSporadic.ON)
    (hmax : ∀ x : Γ, x ^ 3 = 1 → (∀ a ∈ A, a * x = x * a) → x ∈ A) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (A : Set Γ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAL' : A ≤ L := Sec14.ONLoc.le_of_forall_mem hA heA he1 hLe hAL hLq hON3 hmax
  set X := ↥L ⧸ aschbacherSolvableCore 3 ↥L with hXdef
  set θL : Subgroup Γ := inSubgroup (aschbacherSolvableCore 3) L with hθLdef
  have hAθ : A ⊓ θL = ⊥ := Sec14.ONLoc.inf_theta_eq_bot hA.isPGroup
  set ρ : ↥L →* X := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hρdef
  have hρ1 : ∀ y : ↥L, ρ y = 1 ↔ (y : Γ) ∈ θL := by
    intro y
    rw [hρdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨y, h, rfl⟩
    · rintro ⟨y', hy', hyy'⟩
      have : y' = y := Subtype.ext hyy'
      rw [← this]
      exact hy'
  have hρA : ∀ a : ↥L, (a : Γ) ∈ A → ρ a = 1 → (a : Γ) = 1 := by
    intro a ha h1
    have h2 : (a : Γ) ∈ A ⊓ θL := ⟨ha, (hρ1 a).mp h1⟩
    rw [hAθ] at h2
    exact h2
  set Abar : Subgroup X := (A.subgroupOf L).map ρ with hAbardef
  have hAbar27 : Nat.card Abar = 27 := by
    have hinj : Function.Injective (ρ.domRestrict (A.subgroupOf L)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [Subgroup.mem_bot]
      have h1 := hρA a (Subgroup.mem_subgroupOf.mp a.2) ha
      exact Subtype.ext (Subtype.ext h1)
    rw [hAbardef, ← MonoidHom.domRestrict_range]
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL').toEquiv, hA.2]
  have hAbarE : Late.IsE27 Abar := by
    refine ⟨⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, ?_⟩, hAbar27⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := u
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := v
      change ρ x * ρ y = ρ y * ρ x
      have hc : (x : Γ) * y = y * x :=
        congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (hA.1.2 _ (Subgroup.mem_subgroupOf.mp hx))
      rw [this, map_one]
  set C : Subgroup Γ := L ⊓ Subgroup.centralizer (A : Set Γ) with hCdef
  set φ : ↥C →* X := ρ.comp (Subgroup.inclusion (inf_le_left : C ≤ L)) with hφdef
  have hφ9 : ∀ c : ↥C, φ c ^ 9 = 1 := by
    intro c
    have hcent : φ c ∈ Subgroup.centralizer (Abar : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, ha, rfl⟩
      have hcA : (c : Γ) ∈ Subgroup.centralizer (A : Set Γ) := c.2.2
      have h1 := Subgroup.mem_centralizer_iff.mp hcA a (Subgroup.mem_subgroupOf.mp ha)
      change ρ a * ρ (Subgroup.inclusion (inf_le_left : C ≤ L) c) =
        ρ (Subgroup.inclusion (inf_le_left : C ≤ L) c) * ρ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext h1
    exact centralizer_pow_nine_eq_one hLq.1 hON3 hAbarE _ hcent
  have hrange : IsPGroup 3 φ.range := fun y => by
    obtain ⟨c, hc⟩ := y.2
    exact ⟨2, Subtype.ext (by simpa [← hc, ← map_pow] using hφ9 c)⟩
  have hsolR : Group.IsSolvable φ.range := by
    have := hrange.isNilpotent
    infer_instance
  have hsolθ : Group.IsSolvable (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hsolK : Group.IsSolvable φ.ker := by
    let g : φ.ker →* ↥L := (Subgroup.inclusion (inf_le_left : C ≤ L)).comp φ.ker.subtype
    have hg : Function.Injective g := fun u v h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥L => (z : Γ)) h))
    let g' : φ.ker →* aschbacherSolvableCore 3 ↥L :=
      MonoidHom.codRestrict g _ fun k => (QuotientGroup.eq_one_iff _).mp k.2
    exact Group.isSolvable_of_isSolvable_injective (f := g') (fun u v h =>
      hg (congrArg (fun z : ↥(aschbacherSolvableCore 3 ↥L) => (z : ↥L)) h))
  exact Group.isSolvable_of_ker_le_range (φ.ker.subtype) φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.ThreeGroup
