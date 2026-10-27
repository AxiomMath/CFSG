module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

structure s16e_d5_Frame {W : Type} [CommGroup W] (L : Subgroup (MulAut W))
    (K : Fin 4 → Subgroup (MulAut W)) (Z : Fin 4 → Subgroup W) : Prop where
  sq_W : ∀ w : W, w ^ 2 = 1
  elem_L : IsElemAbelianOfRank 3 2 ↥L
  card_L : Nat.card ↥L = 9
  comm_L : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x
  pow_L : ∀ x ∈ L, x ^ 3 = 1
  fixV_L : fixV L = ⊥
  K_le : ∀ i, K i ≤ L
  K_card : ∀ i, Nat.card ↥(K i) = 3
  K_inj : Function.Injective K
  K_all : ∀ H : Subgroup (MulAut W), H ≤ L → Nat.card ↥H = 3 → ∃ i, H = K i
  Z_eq : ∀ i, Z i = fixV (K i)
  Z_rk : ∀ i, rk ↥(Z i) = 2
  Z_indep : iSupIndep Z
  Z_top : (⨆ i, Z i) = ⊤

section FrameLemmas

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private theorem s16e_d5_mem_fixV_zpowers {x : MulAut W} {v : W} :
    v ∈ fixV (Subgroup.zpowers x) ↔ x v = v := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    have hle : Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut W) v := by
      rw [Subgroup.zpowers_le]
      exact h
    exact hle hy

private theorem s16e_d5_toMonoidHom_mul (g h : MulAut W) :
    g.toMonoidHom.comp h.toMonoidHom = (g * h).toMonoidHom := by
  ext v
  rfl

private theorem s16e_d5_map_mul (U : Subgroup W) (g h : MulAut W) :
    (U.map g.toMonoidHom).map h.toMonoidHom = U.map (h * g).toMonoidHom := by
  rw [Subgroup.map_map, s16e_d5_toMonoidHom_mul]

private theorem s16e_d5_one_toMonoidHom :
    (1 : MulAut W).toMonoidHom = MonoidHom.id W :=
  MonoidHom.ext fun _ => rfl

theorem s16e_d5_Frame.card_Z (hfr : s16e_d5_Frame L K Z) (i : Fin 4) :
    Nat.card ↥(Z i) = 4 := by
  rw [card_eq_two_pow hfr.sq_W (Z i), hfr.Z_rk i]
  norm_num

theorem s16e_d5_Frame.Z_ne_bot (hfr : s16e_d5_Frame L K Z) (i : Fin 4) : Z i ≠ ⊥ := by
  intro hbot
  have hcard := hfr.card_Z i
  rw [hbot, Subgroup.card_bot] at hcard
  omega

theorem s16e_d5_Frame.Z_inj (hfr : s16e_d5_Frame L K Z) : Function.Injective Z :=
  hfr.Z_indep.injective hfr.Z_ne_bot

theorem s16e_d5_Frame.stable (hfr : s16e_d5_Frame L K Z) (i : Fin 4) {x : MulAut W}
    (hx : x ∈ L) {z : W} (hz : z ∈ Z i) : x z ∈ Z i := by
  have hzK : z ∈ fixV (K i) := by rwa [← hfr.Z_eq i]
  rw [hfr.Z_eq i]
  refine mem_fixV.mpr fun k hk => ?_
  have hkx : k * x = x * k := hfr.comm_L k (hfr.K_le i hk) x hx
  calc k (x z) = (k * x) z := rfl
    _ = (x * k) z := by rw [hkx]
    _ = x (k z) := rfl
    _ = x z := by rw [(mem_fixV.mp hzK) k hk]

theorem s16e_d5_Frame.no_fix (hfr : s16e_d5_Frame L K Z) (i : Fin 4) {x : MulAut W}
    (hx : x ∈ L) (hxK : x ∉ K i) {z : W} (hz : z ∈ Z i) (hxz : x z = z) : z = 1 := by
  have hx1 : x ≠ 1 := by
    intro h
    exact hxK (by rw [h]; exact (K i).one_mem)
  have hord : orderOf x = 3 := orderOf_eq_prime (hfr.pow_L x hx) hx1
  have hcard : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hord]
  have hzL : Subgroup.zpowers x ≤ L := Subgroup.zpowers_le.mpr hx
  obtain ⟨j, hj⟩ := hfr.K_all (Subgroup.zpowers x) hzL hcard
  have hji : j ≠ i := by
    intro h
    apply hxK
    rw [h] at hj
    rw [← hj]
    exact Subgroup.mem_zpowers x
  have hzj : z ∈ Z j := by
    rw [hfr.Z_eq j, ← hj]
    exact s16e_d5_mem_fixV_zpowers.mpr hxz
  have hdisj : Disjoint (Z i) (Z j) := hfr.Z_indep.pairwiseDisjoint hji.symm
  have hmem : z ∈ Z i ⊓ Z j := Subgroup.mem_inf.mpr ⟨hz, hzj⟩
  rw [disjoint_iff.mp hdisj] at hmem
  simpa using hmem

theorem s16e_d5_Frame.kernel (hfr : s16e_d5_Frame L K Z) (i : Fin 4) {x : MulAut W}
    (hx : x ∈ L) : (∀ z ∈ Z i, x z = z) ↔ x ∈ K i := by
  constructor
  · intro hfix
    by_contra hxK
    have hbot : Z i = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      exact hfr.no_fix i hx hxK hz (hfix z hz)
    exact hfr.Z_ne_bot i hbot
  · intro hxK z hz
    have hzK : z ∈ fixV (K i) := by rwa [← hfr.Z_eq i]
    exact (mem_fixV.mp hzK) x hxK

theorem s16e_d5_Frame.perm (hfr : s16e_d5_Frame L K Z) {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (L : Set (MulAut W))) (i : Fin 4) :
    ∃ j, (Z i).map g.toMonoidHom = Z j := by
  let K' : Subgroup (MulAut W) := (K i).map (MulAut.conj g).toMonoidHom
  have hK'le : K' ≤ L := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hkL : k ∈ L := hfr.K_le i hk
    change (MulAut.conj g) k ∈ L
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg k).mp hkL
  have hK'card : Nat.card ↥K' = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hfr.K_card i]
  obtain ⟨j, hj⟩ := hfr.K_all K' hK'le hK'card
  refine ⟨j, ?_⟩
  calc (Z i).map g.toMonoidHom
      = (fixV (K i)).map g.toMonoidHom := by rw [hfr.Z_eq i]
    _ = fixV K' := (fixV_map_conj_eq (K i) g).symm
    _ = fixV (K j) := by rw [hj]
    _ = Z j := (hfr.Z_eq j).symm

theorem s16e_d5_Frame.trans (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)}
    (hLn : ∀ g ∈ A, g ∈ Subgroup.normalizer (L : Set (MulAut W))) (hind : IsIndivisible A)
    (i j : Fin 4) : ∃ g ∈ A, (Z i).map g.toMonoidHom = Z j := by
  classical
  let O : Set (Fin 4) := {k | ∃ g ∈ A, (Z i).map g.toMonoidHom = Z k}
  have hiO : i ∈ O :=
    ⟨1, A.one_mem, by rw [s16e_d5_one_toMonoidHom, Subgroup.map_id]⟩
  let U₁ : Subgroup W := ⨆ k, ⨆ (_ : k ∈ O), Z k
  let U₂ : Subgroup W := ⨆ k, ⨆ (_ : k ∉ O), Z k
  have hmemO : ∀ (g : MulAut W) (hg : g ∈ A) {k k' : Fin 4}, k ∈ O →
      (Z k).map g.toMonoidHom = Z k' → k' ∈ O := by
    intro g hg k k' hk hmap
    obtain ⟨h, hhA, hh⟩ := hk
    refine ⟨g * h, A.mul_mem hg hhA, ?_⟩
    rw [← s16e_d5_map_mul (Z i) h g, hh, hmap]
  have hnotO : ∀ (g : MulAut W) (hg : g ∈ A) {k k' : Fin 4}, k ∉ O →
      (Z k).map g.toMonoidHom = Z k' → k' ∉ O := by
    intro g hg k k' hk hmap hk'
    obtain ⟨h, hhA, hh⟩ := hk'
    apply hk
    refine ⟨(g⁻¹) * h, A.mul_mem (A.inv_mem hg) hhA, ?_⟩
    rw [← s16e_d5_map_mul (Z i) h (g⁻¹), hh]
    rw [← hmap, s16e_d5_map_mul (Z k) g (g⁻¹)]
    rw [inv_mul_cancel, s16e_d5_one_toMonoidHom, Subgroup.map_id]
  have hstab1 : StableUnder A U₁ := by
    intro g hg u hu
    have hmaple : U₁.map g.toMonoidHom ≤ U₁ := by
      rw [show U₁ = ⨆ k, ⨆ (_ : k ∈ O), Z k from rfl, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun k => iSup_le fun hk => ?_
      obtain ⟨k', hk'⟩ := hfr.perm (hLn g hg) k
      exact le_iSup₂_of_le k' (hmemO g hg hk hk') (le_of_eq hk')
    exact hmaple (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  have hstab2 : StableUnder A U₂ := by
    intro g hg u hu
    have hmaple : U₂.map g.toMonoidHom ≤ U₂ := by
      rw [show U₂ = ⨆ k, ⨆ (_ : k ∉ O), Z k from rfl, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
      refine iSup_le fun k => iSup_le fun hk => ?_
      obtain ⟨k', hk'⟩ := hfr.perm (hLn g hg) k
      exact le_iSup₂_of_le k' (hnotO g hg hk hk') (le_of_eq hk')
    exact hmaple (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  have hU : U₁ ⊔ U₂ = ⊤ := by
    rw [← hfr.Z_top]
    refine le_antisymm ?_ ?_
    · exact sup_le (iSup_le fun k => iSup_le fun _ => le_iSup Z k)
        (iSup_le fun k => iSup_le fun _ => le_iSup Z k)
    · refine iSup_le fun k => ?_
      by_cases hk : k ∈ O
      · exact le_sup_of_le_left (le_iSup₂_of_le k hk le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le k hk le_rfl)
  rcases hind U₁ U₂ hstab1 hstab2 hU with h1 | h2
  · by_contra hcon
    have hjO : j ∉ O := by simpa [O] using hcon
    have hle : Z j ≤ ⨆ k, ⨆ (_ : k ≠ j), Z k := by
      have hjU₁ : Z j ≤ U₁ := by rw [h1]; exact le_top
      refine le_trans hjU₁ ?_
      refine iSup_le fun k => iSup_le fun hkO => ?_
      exact le_iSup₂_of_le k (fun hkj => hjO (hkj ▸ hkO)) le_rfl
    have hbot : Z j = ⊥ := le_bot_iff.mp ((iSupIndep_def.mp hfr.Z_indep j) le_rfl hle)
    exact (hfr.Z_ne_bot j) hbot
  · exfalso
    have hle : Z i ≤ ⨆ k, ⨆ (_ : k ≠ i), Z k := by
      have hiU₂ : Z i ≤ U₂ := by rw [h2]; exact le_top
      refine le_trans hiU₂ ?_
      refine iSup_le fun k => iSup_le fun hkO => ?_
      exact le_iSup₂_of_le k (fun hki => hkO (hki ▸ hiO)) le_rfl
    have hbot : Z i = ⊥ := le_bot_iff.mp ((iSupIndep_def.mp hfr.Z_indep i) le_rfl hle)
    exact (hfr.Z_ne_bot i) hbot

end FrameLemmas

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
