module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs8
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem523DirectAbs6

public section

namespace CFSG.Quasithin.H13.Abs523

variable {E : Type} [CommGroup E] [Finite E]

theorem case_b_false (hH47 : CFSG.ASVolI.H_4_7) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK4 : Nat.card K = 4) (𝒦 : Subgroup (MulAut E)) [IsSimpleGroup ↥𝒦]
    (hab : ¬ IsMulCommutative ↥𝒦) (hcard : 25 ≤ Nat.card ↥𝒦)
    (hiso : Nonempty (↥𝒦 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K))
    (hE2 : ∀ x : E, x ^ 2 = 1) (v : MulAut E) (hvv : v * v = 1)
    (hvN : v ∈ Subgroup.normalizer (𝒦 : Set (MulAut E)))
    (X : Set E) (hXc : X.ncard ≤ 4) (hcm : ∀ x : E, x * (v x)⁻¹ ∈ X)
    (k₁ : MulAut E) (hk₁ : k₁ ∈ 𝒦) (hk₁' : v * k₁ * v⁻¹ ≠ k₁) : False := by
  classical
  have hvv' : ∀ x, v (v x) = x := fun x => by
    have := congrArg (fun F : MulAut E => F x) hvv
    simpa [MulAut.mul_apply] using this
  have hnt : ∃ k ∈ 𝒦, k ≠ 1 := by
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥𝒦)
    exact ⟨g.1, g.2, fun h => hg (Subtype.ext h)⟩
  have hperf : ⁅(⊤ : Subgroup ↥𝒦), (⊤ : Subgroup ↥𝒦)⁆ = ⊤ := by
    haveI : Group.IsPerfect ↥𝒦 := perfect_of_simple_nonab ↥𝒦 hab
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨Y₀, Y₁, hlt, hY₀, hY₁, hirr, hnt'⟩ := exists_section 𝒦 v hvN hperf hnt
  obtain ⟨hY₀i, hY₀v⟩ := hY₀
  obtain ⟨hY₁i, hY₁v⟩ := hY₁
  have h𝒦stab : 𝒦 ≤ stabY Y₀ Y₁ := fun k hk =>
    ⟨fun y => iff_of_inv hY₁i k hk y, fun y => iff_of_inv hY₀i k hk y⟩
  have hvstab : v ∈ stabY Y₀ Y₁ :=
    ⟨fun y => ⟨hY₁v y, fun h => by
        have := hY₁v (v y) h
        rwa [hvv' y] at this⟩,
     fun y => ⟨hY₀v y, fun h => by
        have := hY₀v (v y) h
        rwa [hvv' y] at this⟩⟩
  let ψ : ↥𝒦 →* MulAut (Vsec Y₀ Y₁) := (secHom Y₀ Y₁).comp (Subgroup.inclusion h𝒦stab)
  have hψ : ∀ (k : ↥𝒦) (y : E) (hy : y ∈ Y₁),
      ψ k (vec Y₀ y hy) = vec Y₀ (k.1 y) ((iff_of_inv hY₁i k.1 k.2 y).mp hy) := by
    intro k y hy
    exact secHom_vec ⟨k.1, h𝒦stab k.2⟩ hy
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk, y, hy, hne⟩ := hnt'
      have hker : ψ ⟨k, hk⟩ = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top _)
      have h1 : ψ ⟨k, hk⟩ (vec Y₀ y hy) = vec Y₀ y hy := by
        rw [hker, MulAut.one_apply]
      rw [hψ] at h1
      have h2 : ((k y : E))⁻¹ * y ∈ Y₀ := QuotientGroup.eq.mp (congrArg Subtype.val h1)
      apply hne
      have h3 : k y * y⁻¹ = (((k y : E))⁻¹ * y)⁻¹ := by
        rw [mul_inv, inv_inv]
      rw [h3]
      exact Y₀.inv_mem h2
  have hsimpV : IsSimpleGroup ↥ψ.range := (MonoidHom.ofInjective hψinj).symm.isSimpleGroup
  have hcardV : 25 ≤ Nat.card ↥ψ.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
    exact hcard
  have habV : ¬ IsMulCommutative ↥ψ.range := by
    intro hc
    apply hab
    refine ⟨⟨fun a b => ?_⟩⟩
    apply hψinj
    have h := hc.is_comm.comm ⟨ψ a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
      ⟨ψ b, MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩
    have h' := congrArg Subtype.val h
    simpa [map_mul] using h'
  have hisoV : Nonempty (↥ψ.range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) := by
    obtain ⟨e⟩ := hiso
    exact ⟨(MonoidHom.ofInjective hψinj).symm.trans e⟩
  haveI := hsimpV
  let vV : MulAut (Vsec Y₀ Y₁) := secHom Y₀ Y₁ ⟨v, hvstab⟩
  have hvvV : vV * vV = 1 := by
    show secHom Y₀ Y₁ ⟨v, hvstab⟩ * secHom Y₀ Y₁ ⟨v, hvstab⟩ = 1
    rw [← map_mul, ← map_one (secHom Y₀ Y₁)]
    congr 1
    exact Subtype.ext hvv
  have hvinv : vV⁻¹ = vV := inv_eq_of_mul_eq_one_right hvvV
  have hconj : ∀ k ∈ 𝒦, v * k * v⁻¹ ∈ 𝒦 := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hvN k).mp hk
  have hvinvE : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hvk : ∀ k ∈ 𝒦, v * k * v ∈ 𝒦 := fun k hk => by
    have h := hconj k hk
    rwa [hvinvE] at h
  have hvψ : ∀ k : ↥𝒦, vV * ψ k * vV = ψ ⟨v * k.1 * v, hvk k.1 k.2⟩ := by
    intro k
    have e1 : vV * ψ k * vV = secHom Y₀ Y₁
        (⟨v, hvstab⟩ * ⟨k.1, h𝒦stab k.2⟩ * ⟨v, hvstab⟩) := by
      simp only [map_mul]
      rfl
    rw [e1]
    exact congrArg (secHom Y₀ Y₁) (Subtype.ext rfl)
  have hvNV : vV ∈ Subgroup.normalizer (ψ.range : Set (MulAut (Vsec Y₀ Y₁))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hh
      rw [hvinv, hvψ k]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    · intro hh
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hh
      refine MonoidHom.mem_range.mpr ⟨⟨v * k.1 * v, hvk k.1 k.2⟩, ?_⟩
      rw [← hvψ k, hk, hvinv]
      calc vV * (vV * h * vV) * vV = (vV * vV) * h * (vV * vV) := by group
        _ = h := by rw [hvvV, one_mul, mul_one]
  have hntV : ∃ k' ∈ ψ.range, k' ≠ 1 := by
    obtain ⟨k, hk, hk1⟩ := hnt
    refine ⟨ψ ⟨k, hk⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩, fun h => hk1 ?_⟩
    have h2 : ψ ⟨k, hk⟩ = ψ 1 := by rw [map_one, h]
    exact congrArg Subtype.val (hψinj h2)
  have hvKV : ∃ k' ∈ ψ.range, vV * k' * vV⁻¹ ≠ k' := by
    refine ⟨ψ ⟨k₁, hk₁⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
    rw [hvinv]
    intro h
    rw [hvψ] at h
    have h2 := congrArg Subtype.val (hψinj h)
    apply hk₁'
    rw [hvinvE]
    exact h2
  have hV2 : ∀ x : Vsec Y₀ Y₁, x ^ 2 = 1 := Vsec_sq Y₀ Y₁ hE2
  have hVne : (⊤ : Subgroup (Vsec Y₀ Y₁)) ≠ ⊥ := by
    obtain ⟨y, hyY₁, hyY₀⟩ := SetLike.exists_of_lt hlt
    intro h
    have hmem : vec Y₀ y hyY₁ ∈ (⊤ : Subgroup (Vsec Y₀ Y₁)) := Subgroup.mem_top _
    rw [h, Subgroup.mem_bot] at hmem
    apply hyY₀
    have h2 : ((y : E) : Qt Y₀) = 1 := congrArg Subtype.val hmem
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hirrV : ∀ W : Subgroup (Vsec Y₀ Y₁), (∀ k' ∈ ψ.range, ∀ w ∈ W, k' w ∈ W) →
      (∀ w ∈ W, vV w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hWk hWv
    let Z : Subgroup E :=
      { carrier := {y | ∃ hy : y ∈ Y₁, vec Y₀ y hy ∈ W}
        mul_mem' := fun {a b} ha hb => by
          obtain ⟨ha1, ha2⟩ := ha
          obtain ⟨hb1, hb2⟩ := hb
          refine ⟨Y₁.mul_mem ha1 hb1, ?_⟩
          rw [vec_mul Y₀ ha1 hb1]
          exact W.mul_mem ha2 hb2
        one_mem' := ⟨Y₁.one_mem, by rw [vec_one]; exact W.one_mem⟩
        inv_mem' := fun {a} ha => by
          obtain ⟨ha1, ha2⟩ := ha
          refine ⟨Y₁.inv_mem ha1, ?_⟩
          rw [vec_inv Y₀ ha1]
          exact W.inv_mem ha2 }
    have hZmem : ∀ y : E, y ∈ Z ↔ ∃ hy : y ∈ Y₁, vec Y₀ y hy ∈ W := fun y => Iff.rfl
    have hY0Z : Y₀ ≤ Z := by
      intro y hy
      have hy1 : y ∈ Y₁ := hlt.le hy
      refine (hZmem y).mpr ⟨hy1, ?_⟩
      rw [vec_eq_one_of_mem Y₀ hy1 hy]
      exact W.one_mem
    have hZY1 : Z ≤ Y₁ := fun y hy => ((hZmem y).mp hy).1
    have hZinv : GInv 𝒦 v Z := by
      refine ⟨fun k hk y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨hy1, hyW⟩ := (hZmem y).mp hy
        refine (hZmem (k y)).mpr ⟨(iff_of_inv hY₁i k hk y).mp hy1, ?_⟩
        have h := hWk (ψ ⟨k, hk⟩) (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _ hyW
        rwa [hψ] at h
      · obtain ⟨hy1, hyW⟩ := (hZmem y).mp hy
        refine (hZmem (v y)).mpr ⟨hY₁v y hy1, ?_⟩
        have h := hWv _ hyW
        rwa [show vV (vec Y₀ y hy1) = vec Y₀ (v y) (hY₁v y hy1) from
          secHom_vec ⟨v, hvstab⟩ hy1] at h
    rcases hirr Z hY0Z hZY1 hZinv with hZ | hZ
    · left
      apply Subgroup.ext
      intro w
      constructor
      · intro hw
        obtain ⟨y, hy, hyw⟩ := exists_mk_of_Vsec w
        have hwy : w = vec Y₀ y hy := Subtype.ext hyw.symm
        rw [hwy] at hw
        have hyZ : y ∈ Z := (hZmem y).mpr ⟨hy, hw⟩
        rw [hZ] at hyZ
        rw [Subgroup.mem_bot, hwy]
        exact vec_eq_one_of_mem Y₀ hy hyZ
      · intro hw
        rw [Subgroup.mem_bot] at hw
        rw [hw]
        exact W.one_mem
    · right
      apply Subgroup.ext
      intro w
      constructor
      · intro _
        exact Subgroup.mem_top w
      · intro _
        obtain ⟨y, hy, hyw⟩ := exists_mk_of_Vsec w
        have hwy : w = vec Y₀ y hy := Subtype.ext hyw.symm
        rw [hwy]
        have hyZ : y ∈ Z := by
          rw [hZ]
          exact hy
        exact ((hZmem y).mp hyZ).2
  have hbound : Nat.card ↥(cmSub vV) ≤ 4 := by
    let f : E → Vsec Y₀ Y₁ := fun s => if h : s ∈ Y₁ then vec Y₀ s h else 1
    have hsub : ((cmSub vV : Subgroup (Vsec Y₀ Y₁)) : Set (Vsec Y₀ Y₁)) ⊆
        (fun s => (f s)⁻¹) '' X := by
      intro w hw
      obtain ⟨u, hu⟩ := mem_cmSub.mp hw
      obtain ⟨y, hy, hyu⟩ := exists_mk_of_Vsec u
      have huy : u = vec Y₀ y hy := Subtype.ext hyu.symm
      have hy1 : y * (v y)⁻¹ ∈ Y₁ := Y₁.mul_mem hy (Y₁.inv_mem (hY₁v y hy))
      refine ⟨y * (v y)⁻¹, hcm y, ?_⟩
      show (f (y * (v y)⁻¹))⁻¹ = w
      simp only [f, dif_pos hy1]
      rw [hu, huy, vec_mul Y₀ hy (Y₁.inv_mem (hY₁v y hy)), vec_inv Y₀ (hY₁v y hy)]
      rw [secHom_vec ⟨v, hvstab⟩ hy, mul_inv, inv_inv]
      exact mul_comm _ _
    have h1 : Nat.card ↥(cmSub vV) = ((cmSub vV : Subgroup (Vsec Y₀ Y₁)) : Set (Vsec Y₀ Y₁)).ncard :=
      Nat.card_coe_set_eq _
    rw [h1]
    exact (Set.ncard_le_ncard hsub).trans ((Set.ncard_image_le).trans hXc)
  have hkey := five_le_cmSub hH47 K hK4 hvvV hvNV hV2 habV hisoV hcardV hirrV hVne hntV hvKV
  omega

theorem abs_main (hH47 : CFSG.ASVolI.H_4_7) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK4 : Nat.card K = 4) (𝒦 : Subgroup (MulAut E)) [IsSimpleGroup ↥𝒦]
    (hab : ¬ IsMulCommutative ↥𝒦) (hcard : 25 ≤ Nat.card ↥𝒦)
    (hiso : Nonempty (↥𝒦 ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K))
    (hE2 : ∀ x : E, x ^ 2 = 1) (v : MulAut E) (hvv : v * v = 1)
    (hvN : v ∈ Subgroup.normalizer (𝒦 : Set (MulAut E)))
    (X : Set E) (hXc : X.ncard ≤ 4) (hcm : ∀ x : E, x * (v x)⁻¹ ∈ X) :
    ∀ k ∈ 𝒦, ∀ x : E, k (x * (v x)⁻¹) = x * (v x)⁻¹ := by
  classical
  by_cases hcase : ∀ k ∈ 𝒦, v * k * v⁻¹ = k
  ·
    have hvk : ∀ k ∈ 𝒦, ∀ x : E, v (k x) = k (v x) := by
      intro k hk x
      have h2 : v * k = k * v := by
        calc v * k = (v * k * v⁻¹) * v := by group
          _ = k * v := by rw [hcase k hk]
      have := congrArg (fun F : MulAut E => F x) h2
      simpa [MulAut.mul_apply] using this
    let C : Set E := Set.range (fun x : E => x * (v x)⁻¹)
    have hC : ∀ k ∈ 𝒦, ∀ c ∈ C, k c ∈ C := by
      rintro k hk c ⟨x, rfl⟩
      refine ⟨k x, ?_⟩
      show k x * (v (k x))⁻¹ = k (x * (v x)⁻¹)
      rw [hvk k hk x, map_mul, map_inv]
    have hCc : C.ncard ≤ 4 :=
      (Set.ncard_le_ncard (by rintro _ ⟨x, rfl⟩; exact hcm x)).trans hXc
    intro k hk x
    exact act_trivial_of_small hcard C hC hCc k hk _ ⟨x, rfl⟩
  ·
    exfalso
    push Not at hcase
    obtain ⟨k₁, hk₁, hk₁'⟩ := hcase
    exact case_b_false hH47 K hK4 𝒦 hab hcard hiso hE2 v hvv hvN X hXc hcm k₁ hk₁ hk₁'

end CFSG.Quasithin.H13.Abs523
