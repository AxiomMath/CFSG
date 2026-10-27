module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Descent
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType.Line63.H5

open CFSG.Assembly CFSG.StandardType

theorem isPGroup_three_of_isElemAbelian {X : Type*} [Group X] {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 3 E) : IsPGroup 3 E :=
  fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem exists_sylow_lift {H Q : Type*} [Group H] [Finite H] [Group Q] (π : H →* Q)
    (hker : IsPGroup 2 π.ker) {Sbar : Subgroup Q} (hS : IsPGroup 3 Sbar)
    (hSr : Sbar ≤ π.range) {B : Subgroup H} (hB : IsPGroup 3 B) (hBS : B.map π ≤ Sbar) :
    ∃ S : Subgroup H, B ≤ S ∧ IsPGroup 3 S ∧ S.map π = Sbar ∧
      ∀ s ∈ S, π s = 1 → s = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P : Subgroup H := Sbar.comap π with hP
  have hBP : B ≤ P := fun b hb => hBS ⟨b, hb, rfl⟩
  have hB' : IsPGroup 3 (B.subgroupOf P) := by
    intro g
    obtain ⟨k, hk⟩ := hB ⟨g.1.1, g.2⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  obtain ⟨S', hS'⟩ := hB'.exists_le_sylow
  set S : Subgroup H := (S' : Subgroup ↥P).map P.subtype with hSdef
  have hS3 : IsPGroup 3 S := S'.2.map P.subtype
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  refine ⟨S, ?_, hS3, ?_, ?_⟩
  · intro b hb
    exact ⟨⟨b, hBP hb⟩, hS' (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  · let f : ↥P →* ↥Sbar := (π.comp P.subtype).codRestrict Sbar (fun p => p.2)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      obtain ⟨h, rfl⟩ := hSr hy
      exact ⟨⟨h, hy⟩, Subtype.ext rfl⟩
    have hT : IsPGroup 3 (⊤ : Subgroup ↥Sbar) := by
      intro g
      obtain ⟨k, hk⟩ := hS g.1
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have h1 := (S'.mapSurjective hf).3 hT le_top
    rw [Sylow.coe_mapSurjective] at h1
    have htop : (S' : Subgroup ↥P).map f = ⊤ := h1.symm
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact hSP hs
    · intro y hy
      have hy' : (⟨y, hy⟩ : ↥Sbar) ∈ (S' : Subgroup ↥P).map f := by rw [htop]; trivial
      obtain ⟨p, hp, hpy⟩ := hy'
      exact ⟨p.1, ⟨p, hp, rfl⟩, congrArg Subtype.val hpy⟩
  · intro s hs h1
    have hdisj : Disjoint S π.ker := IsPGroup.disjoint_of_ne 3 2 (by norm_num) S π.ker hS3 hker
    have := hdisj.le_bot ⟨hs, h1⟩
    simpa using this

theorem exists_fixed_lift {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'}
    (hZ : Z ≤ Subgroup.center L') (hZ2 : IsPGroup 2 Z) {a : MulAut L'} (ha3 : a ^ 3 = 1)
    (hZa : ∀ z ∈ Z, a z ∈ Z) {l : L'} (hl : l⁻¹ * a l ∈ Z) :
    ∃ z ∈ Z, a (l * z) = l * z := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut L') :=
    Finite.of_injective (fun φ : MulAut L' => (φ : L' → L')) DFunLike.coe_injective
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZ hy) g
  have hA3 : IsPGroup 3 (Subgroup.zpowers a) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ha3,
      _root_.one_zpow]
  have hpow : ∀ a' ∈ Subgroup.zpowers a, ∃ m : ℕ, a' = a ^ m := by
    intro a' ha'
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff a' a).mp (mem_powers_iff_mem_zpowers.mpr ha')
    exact ⟨m, hm.symm⟩
  have hZpow : ∀ m : ℕ, ∀ z ∈ Z, (a ^ m) z ∈ Z := by
    intro m
    induction m with
    | zero => intro z hz; simpa using hz
    | succ m ih =>
      intro z hz
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hZa z hz)
  have hlpow : ∀ m : ℕ, l⁻¹ * (a ^ m) l ∈ Z := by
    intro m
    induction m with
    | zero => simp [Z.one_mem]
    | succ m ih =>
      have e : l⁻¹ * (a ^ (m + 1)) l = (l⁻¹ * (a ^ m) l) * (a ^ m) (l⁻¹ * a l) := by
        rw [pow_succ, MulAut.mul_apply]
        have h1 : a l = l * (l⁻¹ * a l) := by group
        conv_lhs => rw [h1]
        rw [map_mul]
        group
      rw [e]
      exact Z.mul_mem ih (hZpow m _ hl)
  have hTA : ∀ a' ∈ Subgroup.zpowers a, ∀ t ∈ (⊥ : Subgroup L'), a' t = t := by
    intro a' _ t ht
    rw [Subgroup.mem_bot] at ht
    rw [ht, map_one]
  have hZA : ∀ a' ∈ Subgroup.zpowers a, ∀ z ∈ Z, a' z ∈ Z := by
    intro a' ha' z hz
    obtain ⟨m, rfl⟩ := hpow a' ha'
    exact hZpow m z hz
  have hn₀ : ∀ a' ∈ Subgroup.zpowers a, l * (a' l)⁻¹ ∈ (⊥ : Subgroup L') ⊔ Z := by
    intro a' ha'
    obtain ⟨m, rfl⟩ := hpow a' ha'
    refine Subgroup.mem_sup_right ?_
    set z := l⁻¹ * (a ^ m) l with hz
    have hzm : z ∈ Z := hlpow m
    have hz' : (a ^ m) l = l * z := by rw [hz]; group
    rw [hz']
    have : l * (l * z)⁻¹ = z⁻¹ := by
      calc l * (l * z)⁻¹ = (l * z⁻¹) * l⁻¹ := by group
        _ = (z⁻¹ * l) * l⁻¹ := by rw [hcen z⁻¹ (Z.inv_mem hzm) l]
        _ = z⁻¹ := by group
    rw [this]
    exact Z.inv_mem hzm
  have hT3 : IsPGroup 3 (⊥ : Subgroup L') := fun g => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨z, hz, hzT⟩ := exists_lift_weyl hZ hZ2 hT3 hA3 hZA hTA l hn₀
  refine ⟨z, hz, ?_⟩
  have h1 := hzT a (Subgroup.mem_zpowers a)
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1.symm

theorem map_ggFix_eq_of_lift {L' R : Type} [Group L'] [Finite L'] [Group R] (f : L' →* R)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center L') (hZ2 : IsPGroup 2 f.ker)
    {aγ : MulAut L'} {a : MulAut R} (ha3 : aγ ^ 3 = 1) (hc : ∀ l, a (f l) = f (aγ l)) :
    ggFix a = (ggFix aγ).map f := by
  ext r
  constructor
  · intro hr
    obtain ⟨l, rfl⟩ := hf r
    have h1 : f (aγ l) = f l := by rw [← hc]; exact mem_ggFix.mp hr
    have hz : l⁻¹ * aγ l ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have hZa : ∀ z ∈ f.ker, aγ z ∈ f.ker := by
      intro z hz
      rw [MonoidHom.mem_ker, ← hc, MonoidHom.mem_ker.mp hz, map_one]
    obtain ⟨z, hzk, hfix⟩ := exists_fixed_lift hker hZ2 ha3 hZa hz
    refine ⟨l * z, mem_ggFix.mpr hfix, ?_⟩
    rw [map_mul, MonoidHom.mem_ker.mp hzk, mul_one]
  · rintro ⟨l, hl, rfl⟩
    rw [mem_ggFix, hc, mem_ggFix.mp hl]

theorem isComponentOf_map_of_not_le_ker {H H' : Type*} [Group H] [Group H'] (f : H →* H')
    {K C : Subgroup H} (h : IsComponentOf K C) (hK : ¬ K ≤ f.ker) :
    IsComponentOf (K.map f) (C.map f) := by
  obtain ⟨hKC, hs, hq⟩ := h
  refine ⟨Subgroup.map_mono hKC, hs.map f, ?_⟩
  rw [CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact CFSG.LocalCores.isQuasisimple_map hq f hK

theorem not_le_center_of_isQuasisimple {H : Type*} [Group H] {J : Subgroup H}
    (hq : CFSG.Assembly.IsQuasisimple J) : ¬ J ≤ Subgroup.center H := by
  intro hJ
  have hq' := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq
  obtain ⟨-, -, a, b, hab⟩ := hq'
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine hab ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_center_iff.mp (hJ a.2) b).symm

end CFSG.StandardType.Line63.H5

end
