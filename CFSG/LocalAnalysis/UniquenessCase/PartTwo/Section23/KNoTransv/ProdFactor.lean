module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.ProdDefs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
import CFSG.GroupTheory.PerfectCoverProduct
import TauCeti.GroupTheory.DerivedCentralQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open Subgroup

variable {G S₀ : Type*} [Group G] [Group S₀] {H : Subgroup G}

theorem prodFst_le (g : ↥H →* S₀ × S₀) : prodFst g ≤ H := by
  exact Subgroup.map_subtype_le _

theorem prodSnd_le (g : ↥H →* S₀ × S₀) : prodSnd g ≤ H := by
  exact Subgroup.map_subtype_le _

private theorem prodFst_subgroupOf_eq (g : ↥H →* S₀ × S₀) :
    (prodFst g).subgroupOf H = ((MonoidHom.snd S₀ S₀).comp g).ker := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le (prodFst_le g)]
  rfl

private theorem prodSnd_subgroupOf_eq (g : ↥H →* S₀ × S₀) :
    (prodSnd g).subgroupOf H = ((MonoidHom.fst S₀ S₀).comp g).ker := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_subgroupOf_eq_of_le (prodSnd_le g)]
  rfl

private theorem map_prodFst_subgroupOf_eq (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    ((prodFst g).subgroupOf H).map g = (MonoidHom.snd S₀ S₀).ker := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    rw [prodFst_subgroupOf_eq] at hx
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hg y
    refine ⟨x, ?_, rfl⟩
    rw [prodFst_subgroupOf_eq]
    exact hy

private theorem map_prodSnd_subgroupOf_eq (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    ((prodSnd g).subgroupOf H).map g = (MonoidHom.fst S₀ S₀).ker := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    rw [prodSnd_subgroupOf_eq] at hx
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hg y
    refine ⟨x, ?_, rfl⟩
    rw [prodSnd_subgroupOf_eq]
    exact hy

private theorem isPerfect_ker_snd [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) :
    Group.IsPerfect ↥(MonoidHom.snd S₀ S₀).ker := by
  have hSperf : Group.IsPerfect S₀ :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => by
      obtain ⟨a, b, hab⟩ := hS
      exact hab (hc.is_comm.comm a b)
  letI : Group.IsPerfect S₀ := hSperf
  let f : S₀ →* S₀ × S₀ := (MonoidHom.id S₀).prod (1 : S₀ →* S₀)
  have hrange : f.range = (MonoidHom.snd S₀ S₀).ker := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      rw [MonoidHom.ker_snd]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    · intro hx
      refine ⟨x.1, ?_⟩
      have hx2 : x.2 = 1 := by
        rw [MonoidHom.ker_snd] at hx
        exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx).2
      ext
      · simp [f]
      · simpa [f] using hx2.symm
  have hperfRange : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  letI := hperfRange
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hrange).toMonoidHom)
    (MulEquiv.subgroupCongr hrange).surjective

private theorem isPerfect_ker_fst [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) :
    Group.IsPerfect ↥(MonoidHom.fst S₀ S₀).ker := by
  have hSperf : Group.IsPerfect S₀ :=
    TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative fun hc => by
      obtain ⟨a, b, hab⟩ := hS
      exact hab (hc.is_comm.comm a b)
  letI : Group.IsPerfect S₀ := hSperf
  let f : S₀ →* S₀ × S₀ := (1 : S₀ →* S₀).prod (MonoidHom.id S₀)
  have hrange : f.range = (MonoidHom.fst S₀ S₀).ker := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      rw [MonoidHom.ker_fst]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top a⟩
    · intro hx
      refine ⟨x.2, ?_⟩
      have hx1 : x.1 = 1 := by
        rw [MonoidHom.ker_fst] at hx
        exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hx).1
      ext
      · simpa [f] using hx1.symm
      · simp [f]
  have hperfRange : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  letI := hperfRange
  exact Group.IsPerfect.ofSurjective (f := (MulEquiv.subgroupCongr hrange).toMonoidHom)
    (MulEquiv.subgroupCongr hrange).surjective

private theorem exists_mul_of_mem_prodFst [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) {x : ↥H} (hx : x ∈ (prodFst g).subgroupOf H) :
    ∃ y ∈ ⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆,
      ∃ z ∈ g.ker, x = y * z := by
  have hL : ⁅(MonoidHom.snd S₀ S₀).ker, (MonoidHom.snd S₀ S₀).ker⁆ =
      (MonoidHom.snd S₀ S₀).ker := by
    haveI := isPerfect_ker_snd hS
    exact Subgroup.commutator_eq_self
  have hK : (prodFst g).subgroupOf H = ((MonoidHom.snd S₀ S₀).ker).comap g := by
    rw [prodFst_subgroupOf_eq, MonoidHom.comap_ker]
  obtain ⟨y, hy, z, hz, hxy⟩ :=
    CFSG.GroupTheory.PerfectCover.exists_mul_of_mem_comap (π := g) hg hL (hK ▸ hx)
  exact ⟨y, hK.symm ▸ hy, z, hz, hxy⟩

private theorem exists_mul_of_mem_prodSnd [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) {x : ↥H} (hx : x ∈ (prodSnd g).subgroupOf H) :
    ∃ y ∈ ⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆,
      ∃ z ∈ g.ker, x = y * z := by
  have hL : ⁅(MonoidHom.fst S₀ S₀).ker, (MonoidHom.fst S₀ S₀).ker⁆ =
      (MonoidHom.fst S₀ S₀).ker := by
    haveI := isPerfect_ker_fst hS
    exact Subgroup.commutator_eq_self
  have hK : (prodSnd g).subgroupOf H = ((MonoidHom.fst S₀ S₀).ker).comap g := by
    rw [prodSnd_subgroupOf_eq, MonoidHom.comap_ker]
  obtain ⟨y, hy, z, hz, hxy⟩ :=
    CFSG.GroupTheory.PerfectCover.exists_mul_of_mem_comap (π := g) hg hL (hK ▸ hx)
  exact ⟨y, hK.symm ▸ hy, z, hz, hxy⟩

theorem commutator_commutator_prodFst [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) :
    ⁅⁅prodFst g, prodFst g⁆, ⁅prodFst g, prodFst g⁆⁆ = ⁅prodFst g, prodFst g⁆ := by
  let K : Subgroup ↥H := (prodFst g).subgroupOf H
  have hL : ⁅(MonoidHom.snd S₀ S₀).ker, (MonoidHom.snd S₀ S₀).ker⁆ =
      (MonoidHom.snd S₀ S₀).ker := by
    haveI := isPerfect_ker_snd hS
    exact Subgroup.commutator_eq_self
  have hperfH : Group.IsPerfect ↥⁅K, K⁆ := by
    change Group.IsPerfect
      ↥⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆
    rw [prodFst_subgroupOf_eq, ← MonoidHom.comap_ker]
    exact CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap g hg hker hL
  have hmap : (⁅K, K⁆).map H.subtype = ⁅prodFst g, prodFst g⁆ := by
    change (⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆).map H.subtype = _
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (prodFst_le g)]
  have hperfG : Group.IsPerfect ↥⁅prodFst g, prodFst g⁆ := by
    haveI := hperfH
    rw [← hmap]
    exact Group.IsPerfect.map (H := ⁅K, K⁆) (H.subtype : ↥H →* G)
  letI := hperfG
  exact Subgroup.commutator_eq_self

theorem commutator_commutator_prodSnd [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) :
    ⁅⁅prodSnd g, prodSnd g⁆, ⁅prodSnd g, prodSnd g⁆⁆ = ⁅prodSnd g, prodSnd g⁆ := by
  let K : Subgroup ↥H := (prodSnd g).subgroupOf H
  have hL : ⁅(MonoidHom.fst S₀ S₀).ker, (MonoidHom.fst S₀ S₀).ker⁆ =
      (MonoidHom.fst S₀ S₀).ker := by
    haveI := isPerfect_ker_fst hS
    exact Subgroup.commutator_eq_self
  have hperfH : Group.IsPerfect ↥⁅K, K⁆ := by
    change Group.IsPerfect
      ↥⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆
    rw [prodSnd_subgroupOf_eq, ← MonoidHom.comap_ker]
    exact CFSG.GroupTheory.PerfectCover.isPerfect_commutator_comap g hg hker hL
  have hmap : (⁅K, K⁆).map H.subtype = ⁅prodSnd g, prodSnd g⁆ := by
    change (⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆).map H.subtype = _
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (prodSnd_le g)]
  have hperfG : Group.IsPerfect ↥⁅prodSnd g, prodSnd g⁆ := by
    haveI := hperfH
    rw [← hmap]
    exact Group.IsPerfect.map (H := ⁅K, K⁆) (H.subtype : ↥H →* G)
  letI := hperfG
  exact Subgroup.commutator_eq_self

theorem exists_hom_prodFst [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) :
    ∃ f₀ : ↥⁅prodFst g, prodFst g⁆ →* S₀,
      Function.Surjective f₀ ∧ f₀.ker ≤ center ↥⁅prodFst g, prodFst g⁆ := by
  let K : Subgroup G := ⁅prodFst g, prodFst g⁆
  let K' : Subgroup ↥H := ⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆
  have hle : K ≤ H :=
    (Subgroup.commutator_le_self (prodFst g)).trans (prodFst_le g)
  have hKmap : K'.map H.subtype = K := by
    change (⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆).map H.subtype = _
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (prodFst_le g)]
  have hL : ⁅(MonoidHom.snd S₀ S₀).ker, (MonoidHom.snd S₀ S₀).ker⁆ =
      (MonoidHom.snd S₀ S₀).ker := by
    haveI := isPerfect_ker_snd hS
    exact Subgroup.commutator_eq_self
  have hmapKer : K'.map g = (MonoidHom.snd S₀ S₀).ker := by
    change (⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆).map g = _
    rw [Subgroup.map_commutator, map_prodFst_subgroupOf_eq g hg, hL]
  let f₀ : ↥K →* S₀ := (MonoidHom.fst S₀ S₀).comp (g.comp (Subgroup.inclusion hle))
  refine ⟨f₀, ?_, ?_⟩
  · intro a
    have hmem : (a, 1) ∈ (MonoidHom.snd S₀ S₀).ker := by
      rw [MonoidHom.ker_snd]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
    rw [← hmapKer] at hmem
    obtain ⟨x, hx, hxg⟩ := hmem
    have hxK : (x : G) ∈ K := by
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem H.subtype hx
    refine ⟨⟨(x : G), hxK⟩, ?_⟩
    have hincl : (Subgroup.inclusion hle ⟨(x : G), hxK⟩ : ↥H) = x := Subtype.ext rfl
    change (g (Subgroup.inclusion hle ⟨(x : G), hxK⟩)).1 = a
    rw [hincl, hxg]
  · intro x hx
    let xH : ↥H := ⟨x.val, hle x.2⟩
    have hxK' : xH ∈ K' := by
      have hxmap : (xH : G) ∈ K'.map H.subtype := by
        rw [hKmap]
        exact x.2
      obtain ⟨z, hz, hzval⟩ := hxmap
      have hzx : z = xH := Subtype.ext hzval
      simpa [hzx] using hz
    have hinclx : (Subgroup.inclusion hle x : ↥H) = xH := Subtype.ext rfl
    have hx1 : (g xH).1 = 1 := by
      rw [← hinclx]
      simpa [f₀] using hx
    have hx2 : (g xH).2 = 1 := by
      have hmem : xH ∈ (prodFst g).subgroupOf H :=
        Subgroup.commutator_le_self ((prodFst g).subgroupOf H) hxK'
      rwa [prodFst_subgroupOf_eq] at hmem
    have hxker : xH ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      ext <;> assumption
    have hxcenter := hker hxker
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hcent : (⟨y.val, hle y.2⟩ : ↥H) * xH = xH * ⟨y.val, hle y.2⟩ :=
      Subgroup.mem_center_iff.mp hxcenter ⟨y.val, hle y.2⟩
    have hcent' : y.val * x.val = x.val * y.val := congrArg Subtype.val hcent
    simpa using hcent'

theorem exists_hom_prodSnd [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H) :
    ∃ f₀ : ↥⁅prodSnd g, prodSnd g⁆ →* S₀,
      Function.Surjective f₀ ∧ f₀.ker ≤ center ↥⁅prodSnd g, prodSnd g⁆ := by
  let K : Subgroup G := ⁅prodSnd g, prodSnd g⁆
  let K' : Subgroup ↥H := ⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆
  have hle : K ≤ H :=
    (Subgroup.commutator_le_self (prodSnd g)).trans (prodSnd_le g)
  have hKmap : K'.map H.subtype = K := by
    change (⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆).map H.subtype = _
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (prodSnd_le g)]
  have hL : ⁅(MonoidHom.fst S₀ S₀).ker, (MonoidHom.fst S₀ S₀).ker⁆ =
      (MonoidHom.fst S₀ S₀).ker := by
    haveI := isPerfect_ker_fst hS
    exact Subgroup.commutator_eq_self
  have hmapKer : K'.map g = (MonoidHom.fst S₀ S₀).ker := by
    change (⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆).map g = _
    rw [Subgroup.map_commutator, map_prodSnd_subgroupOf_eq g hg, hL]
  let f₀ : ↥K →* S₀ := (MonoidHom.snd S₀ S₀).comp (g.comp (Subgroup.inclusion hle))
  refine ⟨f₀, ?_, ?_⟩
  · intro a
    have hmem : (1, a) ∈ (MonoidHom.fst S₀ S₀).ker := by
      rw [MonoidHom.ker_fst]
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top a⟩
    rw [← hmapKer] at hmem
    obtain ⟨x, hx, hxg⟩ := hmem
    have hxK : (x : G) ∈ K := by
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem H.subtype hx
    refine ⟨⟨(x : G), hxK⟩, ?_⟩
    have hincl : (Subgroup.inclusion hle ⟨(x : G), hxK⟩ : ↥H) = x := Subtype.ext rfl
    change (g (Subgroup.inclusion hle ⟨(x : G), hxK⟩)).2 = a
    rw [hincl, hxg]
  · intro x hx
    let xH : ↥H := ⟨x.val, hle x.2⟩
    have hxK' : xH ∈ K' := by
      have hxmap : (xH : G) ∈ K'.map H.subtype := by
        rw [hKmap]
        exact x.2
      obtain ⟨z, hz, hzval⟩ := hxmap
      have hzx : z = xH := Subtype.ext hzval
      simpa [hzx] using hz
    have hinclx : (Subgroup.inclusion hle x : ↥H) = xH := Subtype.ext rfl
    have hx1 : (g xH).1 = 1 := by
      have hmem : xH ∈ (prodSnd g).subgroupOf H :=
        Subgroup.commutator_le_self ((prodSnd g).subgroupOf H) hxK'
      rwa [prodSnd_subgroupOf_eq] at hmem
    have hx2 : (g xH).2 = 1 := by
      rw [← hinclx]
      simpa [f₀] using hx
    have hxker : xH ∈ g.ker := by
      rw [MonoidHom.mem_ker]
      ext <;> assumption
    have hxcenter := hker hxker
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hcent : (⟨y.val, hle y.2⟩ : ↥H) * xH = xH * ⟨y.val, hle y.2⟩ :=
      Subgroup.mem_center_iff.mp hxcenter ⟨y.val, hle y.2⟩
    have hcent' : y.val * x.val = x.val * y.val := congrArg Subtype.val hcent
    simpa using hcent'

private theorem prodFst_le_commutator_sup_ker [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    (prodFst g).subgroupOf H ≤
      ⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆ ⊔ g.ker := by
  intro x hx
  obtain ⟨y, hy, z, hz, hxz⟩ := exists_mul_of_mem_prodFst hS g hg hx
  exact Subgroup.mem_sup_of_normal_right.mpr ⟨y, hy, z, hz, hxz.symm⟩

private theorem prodSnd_le_commutator_sup_ker [IsSimpleGroup S₀]
    (hS : ∃ a b : S₀, a * b ≠ b * a) (g : ↥H →* S₀ × S₀)
    (hg : Function.Surjective g) :
    (prodSnd g).subgroupOf H ≤
      ⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆ ⊔ g.ker := by
  intro x hx
  obtain ⟨y, hy, z, hz, hxz⟩ := exists_mul_of_mem_prodSnd hS g hg hx
  exact Subgroup.mem_sup_of_normal_right.mpr ⟨y, hy, z, hz, hxz.symm⟩

theorem le_sup_commutator [IsSimpleGroup S₀] (hS : ∃ a b : S₀, a * b ≠ b * a)
    (g : ↥H →* S₀ × S₀) (hg : Function.Surjective g) (hker : g.ker ≤ center ↥H)
    (hH : ⁅H, H⁆ = H) :
    H ≤ ⁅prodFst g, prodFst g⁆ ⊔ ⁅prodSnd g, prodSnd g⁆ := by
  classical
  let K₁ : Subgroup ↥H := (prodFst g).subgroupOf H
  let K₂ : Subgroup ↥H := (prodSnd g).subgroupOf H
  let Z : Subgroup ↥H := g.ker
  let L : Subgroup ↥H := ⁅K₁, K₁⁆ ⊔ ⁅K₂, K₂⁆
  have hK₁ : (prodFst g).subgroupOf H ≤
      ⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆ ⊔ g.ker :=
    prodFst_le_commutator_sup_ker hS g hg
  have hK₂ : (prodSnd g).subgroupOf H ≤
      ⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆ ⊔ g.ker :=
    prodSnd_le_commutator_sup_ker hS g hg
  have hHle : (⊤ : Subgroup ↥H) ≤ L ⊔ Z := by
    intro x _
    obtain ⟨a₁, ha₁g⟩ := hg ((g x).1, 1)
    obtain ⟨a₂, ha₂g⟩ := hg (1, (g x).2)
    have ha₁ : a₁ ∈ K₁ := by
      change a₁ ∈ (prodFst g).subgroupOf H
      rw [prodFst_subgroupOf_eq]
      exact congrArg Prod.snd ha₁g
    have ha₂ : a₂ ∈ K₂ := by
      change a₂ ∈ (prodSnd g).subgroupOf H
      rw [prodSnd_subgroupOf_eq]
      exact congrArg Prod.fst ha₂g
    have hz : (a₁ * a₂)⁻¹ * x ∈ Z := by
      change g ((a₁ * a₂)⁻¹ * x) = 1
      rw [map_mul, map_inv, map_mul, ha₁g, ha₂g]
      simp
    have hxeq : x = a₁ * a₂ * ((a₁ * a₂)⁻¹ * x) := by group
    have ha₁L : a₁ ∈ L ⊔ Z :=
      (sup_le_sup (show ⁅K₁, K₁⁆ ≤ L from le_sup_left) le_rfl) (hK₁ ha₁)
    have ha₂L : a₂ ∈ L ⊔ Z :=
      (sup_le_sup (show ⁅K₂, K₂⁆ ≤ L from le_sup_right) le_rfl) (hK₂ ha₂)
    have hzL : (a₁ * a₂)⁻¹ * x ∈ L ⊔ Z := Subgroup.mem_sup_right hz
    rw [hxeq]
    exact (L ⊔ Z).mul_mem ((L ⊔ Z).mul_mem ha₁L ha₂L) hzL
  have hcomm : ⁅L ⊔ Z, L ⊔ Z⁆ ≤ L := by
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    obtain ⟨l₁, hl₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨l₂, hl₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    rw [CFSG.GroupTheory.PerfectCover.commutatorElement_mul_mul_of_mem_center
      (hker hz₁) (hker hz₂)]
    exact (Subgroup.commutator_le_self L) (Subgroup.commutator_mem_commutator hl₁ hl₂)
  haveI : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hH
  have htopL : (⊤ : Subgroup ↥H) ≤ L := by
    have htop : (⊤ : Subgroup ↥H) = ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := by
      rw [← commutator_def]
      exact (Group.IsPerfect.commutator_eq_top).symm
    calc
      (⊤ : Subgroup ↥H) = ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ := htop
      _ ≤ ⁅L ⊔ Z, L ⊔ Z⁆ := Subgroup.commutator_mono hHle hHle
      _ ≤ L := hcomm
  have hmapL : L.map H.subtype =
      ⁅prodFst g, prodFst g⁆ ⊔ ⁅prodSnd g, prodSnd g⁆ := by
    change (⁅(prodFst g).subgroupOf H, (prodFst g).subgroupOf H⁆ ⊔
      ⁅(prodSnd g).subgroupOf H, (prodSnd g).subgroupOf H⁆).map H.subtype = _
    rw [Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (prodFst_le g),
      Subgroup.map_subgroupOf_eq_of_le (prodSnd_le g)]
  have htop_eq : (⊤ : Subgroup ↥H).map H.subtype = H := by
    simpa using (Subgroup.map_subgroupOf_eq_of_le (H := H) (K := H) le_rfl)
  have htopmap := Subgroup.map_mono (f := H.subtype) htopL
  rw [htop_eq, hmapL] at htopmap
  exact htopmap

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
