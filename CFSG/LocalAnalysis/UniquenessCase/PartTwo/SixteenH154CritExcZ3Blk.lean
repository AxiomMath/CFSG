module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.Quasithin.EmptyFaithful.S151bModule

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

structure s16h_Z3Blocks {W : Type} [CommGroup W] (A L L₂ : Subgroup (MulAut W))
    (x : MulAut W) : Prop where
  mem : x ∈ A
  eq : L₂ = L.map (MulAut.conj x).toMonoidHom
  ne : L₂ ≠ L
  perm : ∀ g ∈ A,
    (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
    (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L)
  sup : commSub (⊤ : Subgroup W) L ⊔ commSub (⊤ : Subgroup W) L₂ = ⊤
  inf : commSub (⊤ : Subgroup W) L ⊓ commSub (⊤ : Subgroup W) L₂ = ⊥
  cent₂ : L₂ ≤ centSub (commSub (⊤ : Subgroup W) L)
  cent₁ : L ≤ centSub (commSub (⊤ : Subgroup W) L₂)
  swap : ∀ u : W, u ∈ commSub (⊤ : Subgroup W) L ↔ x u ∈ commSub (⊤ : Subgroup W) L₂
  swap' : ∀ u : W, u ∈ commSub (⊤ : Subgroup W) L₂ ↔ x u ∈ commSub (⊤ : Subgroup W) L
  stab : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L →
    g ∈ stabSub (commSub (⊤ : Subgroup W) L) ∧ g ∈ stabSub (commSub (⊤ : Subgroup W) L₂)
  card_eq : Nat.card ↥L₂ = Nat.card ↥L
  rk_eq : rk ↥(commSub (⊤ : Subgroup W) L₂) = rk ↥(commSub (⊤ : Subgroup W) L)
  fix_iff : commSub (⊤ : Subgroup W) L₂ ⊓ fixV L₂ = ⊥ ↔
    commSub (⊤ : Subgroup W) L ⊓ fixV L = ⊥

theorem s16h_z3_blocks {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : Conc4_136W A t L)
    (hind : sSupIndep (conjSubs A (commSub (⊤ : Subgroup W) L))) {x : MulAut W} (hxA : x ∈ A)
    (hxL : L.map (MulAut.conj x).toMonoidHom ≠ L)
    (hperm : ∀ g ∈ A,
      (L.map (MulAut.conj g).toMonoidHom = L ∧
        (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom =
          L.map (MulAut.conj x).toMonoidHom) ∨
      (L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj x).toMonoidHom ∧
        (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom = L)) :
    s16h_Z3Blocks A L (L.map (MulAut.conj x).toMonoidHom) x := by
  classical
  set L₂ := L.map (MulAut.conj x).toMonoidHom with hL₂def
  set U := commSub (⊤ : Subgroup W) L with hUdef
  set U₂ := commSub (⊤ : Subgroup W) L₂ with hU₂def
  have hxL₂ : L₂.map (MulAut.conj x).toMonoidHom = L := by
    rcases hperm x hxA with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact absurd h1 hxL
    · exact h2
  have hcomp_inv_x : ((MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom) =
      MonoidHom.id (MulAut W) := by
    ext l
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom]
    group
  have hxinvL : L.map (MulAut.conj x⁻¹).toMonoidHom = L₂ := by
    have h := congrArg (fun K : Subgroup (MulAut W) => K.map (MulAut.conj x⁻¹).toMonoidHom) hxL₂
    rw [Subgroup.map_map] at h
    rw [hcomp_inv_x, Subgroup.map_id] at h
    exact h.symm
  have hswap : ∀ u : W, u ∈ U ↔ x u ∈ U₂ := by
    intro u
    constructor
    · intro hu
      exact commSub_top_map151b (X := L) (Y := L₂) (g := x)
        (fun l hl => Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hl) u hu
    · intro hu
      have hmem : x⁻¹ (x u) ∈ commSub (⊤ : Subgroup W) L :=
        commSub_top_map151b (X := L₂) (Y := L) (g := x⁻¹)
          (fun l₂ hl₂ => by
            obtain ⟨l, hl, hl2⟩ := Subgroup.mem_map.mp hl₂
            rw [← hl2]
            have h' : x⁻¹ * ((MulAut.conj x).toMonoidHom l) * x = l := by
              simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
              group
            rw [inv_inv]
            rwa [h']) (x u) hu
      simpa using hmem
  have hswap' : ∀ u : W, u ∈ U₂ ↔ x u ∈ U := by
    intro u
    constructor
    · intro hu
      exact commSub_top_map151b (X := L₂) (Y := L) (g := x)
        (fun l₂ hl₂ => by
          have h := Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hl₂
          rwa [hxL₂] at h) u hu
    · intro hu
      have hmem : x⁻¹ (x u) ∈ commSub (⊤ : Subgroup W) L₂ :=
        commSub_top_map151b (X := L) (Y := L₂) (g := x⁻¹)
          (fun l hl => by
            have h := Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hl
            rwa [hxinvL] at h) (x u) hu
      simpa using hmem
  have hU₂_eq : U₂ = U.map x.toMonoidHom := by
    ext v
    constructor
    · intro hv
      refine ⟨x⁻¹ v, ?_, by simp⟩
      exact (hswap (x⁻¹ v)).mpr (by simpa using hv)
    · rintro ⟨u, hu, rfl⟩
      exact (hswap u).mp hu
  have hxn : x ∉ normalizer (L : Set (MulAut W)) := by
    intro hxN
    exact hxL (Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN)
  have hcent₂ : L₂ ≤ centSub U := by
    have h := (hc.2.1 x hxA hxn).2
    change commSub U L₂ = ⊥ at h
    rw [commSub_eq_bot_iff] at h
    intro l₂ hl₂ u hu
    exact (mem_fixV.mp (h hu)) l₂ hl₂
  have hxn' : x⁻¹ ∉ normalizer (L : Set (MulAut W)) := by
    intro hxN
    have hxL' : L.map (MulAut.conj x⁻¹).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    have h := congrArg (fun K : Subgroup (MulAut W) => K.map (MulAut.conj x).toMonoidHom) hxL'
    rw [Subgroup.map_map] at h
    have hcomp_x_inv : ((MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom) =
        MonoidHom.id (MulAut W) := by
      ext l
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulAut.conj_apply,
        MulEquiv.coe_toMonoidHom]
      group
    rw [hcomp_x_inv, Subgroup.map_id] at h
    exact hxL h.symm
  have hcent₁ : L ≤ centSub U₂ := by
    have h2 : commSub U (L.map (MulAut.conj x⁻¹).toMonoidHom) = ⊥ :=
      (hc.2.1 x⁻¹ (A.inv_mem hxA) hxn').2
    rw [commSub_eq_bot_iff] at h2
    intro l hl u₂ hu₂
    have hu : x⁻¹ u₂ ∈ U := (hswap (x⁻¹ u₂)).mpr (by simpa using hu₂)
    have hlx_mem : x⁻¹ * l * x ∈ L.map (MulAut.conj x⁻¹).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hl
    have hfix : (x⁻¹ * l * x) (x⁻¹ u₂) = x⁻¹ u₂ :=
      (mem_fixV.mp (h2 hu)) (x⁻¹ * l * x) hlx_mem
    calc l u₂ = x ((x⁻¹ * l * x) (x⁻¹ u₂)) := by simp [MulAut.mul_apply]
      _ = x (x⁻¹ u₂) := by rw [hfix]
      _ = u₂ := by simp
  have hsup : U ⊔ U₂ = ⊤ := by
    have hc1 : (⨆ X ∈ conjSubs A U, X) = ⊤ := hc.1
    have hle : (⨆ X ∈ conjSubs A U, X) ≤ U ⊔ U₂ := by
      refine iSup₂_le fun X hX => ?_
      obtain ⟨g, hgA, rfl⟩ := hX
      rcases hperm g hgA with ⟨h1, -⟩ | ⟨h1, -⟩
      · have hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
          intro l hl
          have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hl
          rwa [h1] at this
        intro y hy
        obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_sup_left (commSub_top_stable151b hg c hc')
      · have hg : ∀ l ∈ L, g * l * g⁻¹ ∈ L₂ := by
          intro l hl
          have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hl
          rwa [h1] at this
        intro y hy
        obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_sup_right (commSub_top_map151b hg c hc')
    rw [eq_top_iff, ← hc1]
    exact hle
  have hcent_top : centSub (⊤ : Subgroup W) = ⊥ := by
    ext g
    rw [Subgroup.mem_bot, mem_centSub]
    constructor
    · intro hg
      ext w
      exact hg w (Subgroup.mem_top w)
    · intro hg w _
      rw [hg]
      rfl
  have hL_eq : L = L₂.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [hL₂def, Subgroup.map_map, hcomp_inv_x, Subgroup.map_id]
  have hU_ne : U ≠ U₂ := by
    intro hUU₂
    have hU_top : U = ⊤ := by
      have h := hsup
      rw [← hUU₂, sup_idem] at h
      exact h
    have hL₂_bot : L₂ = ⊥ := by
      have h : L₂ ≤ centSub U := hcent₂
      rw [hU_top, hcent_top] at h
      exact le_bot_iff.mp h
    have hL_bot : L = ⊥ := by
      rw [hL_eq, hL₂_bot]
      simp
    exact hxL (hL₂_bot.trans hL_bot.symm)
  have hinf : U ⊓ U₂ = ⊥ := by
    have hU_mem : U ∈ conjSubs A U := ⟨1, A.one_mem, by ext; simp⟩
    have hU₂_mem : U₂ ∈ conjSubs A U := ⟨x, hxA, hU₂_eq⟩
    have hdis := hind.pairwiseDisjoint hU_mem hU₂_mem hU_ne
    exact disjoint_iff.mp hdis
  have hstab : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L →
      g ∈ stabSub U ∧ g ∈ stabSub U₂ := by
    intro g hgA hgL
    have hgL₂ : L₂.map (MulAut.conj g).toMonoidHom = L₂ := by
      rcases hperm g hgA with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2
      · exfalso
        exact hxL (hgL.symm.trans h1).symm
    have hgN : g ∈ normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgL
    have hginvN : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
      (normalizer (L : Set (MulAut W))).inv_mem hgN
    have hginvL : L.map (MulAut.conj g⁻¹).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hginvN
    have hg_norm : ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
      intro l hl
      have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hl
      rwa [hgL] at this
    have hginv_norm : ∀ l ∈ L, g⁻¹ * l * (g⁻¹)⁻¹ ∈ L := by
      intro l hl
      have := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hl
      rwa [hginvL] at this
    have hg_stab_U : g ∈ stabSub U := by
      rw [mem_stabSub]
      intro u
      constructor
      · intro hgu
        have h := commSub_top_stable151b hginv_norm (g u) hgu
        simpa using h
      · intro hu
        exact commSub_top_stable151b hg_norm u hu
    have hg₂N : g ∈ normalizer (L₂ : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgL₂
    have hginv₂N : g⁻¹ ∈ normalizer (L₂ : Set (MulAut W)) :=
      (normalizer (L₂ : Set (MulAut W))).inv_mem hg₂N
    have hginvL₂ : L₂.map (MulAut.conj g⁻¹).toMonoidHom = L₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hginv₂N
    have hg₂_norm : ∀ l ∈ L₂, g * l * g⁻¹ ∈ L₂ := by
      intro l hl
      have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hl
      rwa [hgL₂] at this
    have hginv₂_norm : ∀ l ∈ L₂, g⁻¹ * l * (g⁻¹)⁻¹ ∈ L₂ := by
      intro l hl
      have := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hl
      rwa [hginvL₂] at this
    have hg_stab_U₂ : g ∈ stabSub U₂ := by
      rw [mem_stabSub]
      intro u
      constructor
      · intro hgu
        have h := commSub_top_stable151b hginv₂_norm (g u) hgu
        simpa using h
      · intro hu
        exact commSub_top_stable151b hg₂_norm u hu
    exact ⟨hg_stab_U, hg_stab_U₂⟩
  have hcard_eq : Nat.card ↥L₂ = Nat.card ↥L := by
    rw [hL₂def]
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hrk_eq : rk ↥U₂ = rk ↥U := by
    unfold rk
    rw [hU₂_eq, Subgroup.card_map_of_injective x.injective]
  have hfix_map : U₂ ⊓ fixV L₂ = (U ⊓ fixV L).map x.toMonoidHom := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvU₂, hvfix⟩ := Subgroup.mem_inf.mp hv
      have hvU₂' : v ∈ U.map x.toMonoidHom := by rwa [hU₂_eq] at hvU₂
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hvU₂'
      refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
      intro l hl
      have hlx : x * l * x⁻¹ ∈ L₂ :=
        Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hl
      have hfixx : (x * l * x⁻¹) (x u) = x u :=
        (mem_fixV.mp hvfix) (x * l * x⁻¹) hlx
      have h' : x (l u) = x u := by simpa [MulAut.mul_apply] using hfixx
      exact x.injective h'
    · rintro ⟨u, ⟨hu, hfu⟩, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [hU₂_eq]
        exact Subgroup.mem_map_of_mem x.toMonoidHom hu
      · intro l₂ hl₂
        rw [hL₂def] at hl₂
        obtain ⟨l, hl, hl2⟩ := Subgroup.mem_map.mp hl₂
        rw [← hl2]
        have hlu : l u = u := (mem_fixV.mp hfu) l hl
        show (x * l * x⁻¹) (x u) = x u
        simp [MulAut.mul_apply, hlu]
  have hfix_iff : U₂ ⊓ fixV L₂ = ⊥ ↔ U ⊓ fixV L = ⊥ := by
    rw [hfix_map]
    exact Subgroup.map_eq_bot_iff_of_injective (U ⊓ fixV L) x.injective
  exact ⟨hxA, rfl, hxL, hperm, hsup, hinf, hcent₂, hcent₁, hswap, hswap', hstab,
    hcard_eq, hrk_eq, hfix_iff⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
