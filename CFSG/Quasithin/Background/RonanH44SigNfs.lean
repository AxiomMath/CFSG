module

public import CFSG.Quasithin.Background.RonanH44SigSec
public import CFSG.Quasithin.Background.RonanH44SigFaith
public import CFSG.Quasithin.Background.RonanH44Nfs

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem sigG_facts (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {g : MulAut (HMod n K)}
    (hg : g ∈ img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))) :
    (∀ v ∈ fixV (Subgroup.zpowers (sig n K)), g v ∈ fixV (Subgroup.zpowers (sig n K))) ∧
    (∀ v ∈ commV (Subgroup.zpowers (sig n K)), g v ∈ commV (Subgroup.zpowers (sig n K))) ∧
    (∀ (c : Fq n K) (v w : HMod n K), mat w = scalF n K c • mat v →
      mat (g w) = scalF n K c • mat (g v)) ∧
    ∃ h : SL(3, Fq n K), rhoF hK h = g := by
  obtain ⟨hL, hC⟩ := Subgroup.mem_inf.mp hg
  have hcomm : sig n K * g = g * sig n K :=
    Subgroup.mem_centralizer_iff.1 hC (sig n K) (Set.mem_singleton _)
  have happ : ∀ v : HMod n K, sig n K (g v) = g (sig n K v) := fun v =>
    congrArg (fun φ : MulAut (HMod n K) => φ v) hcomm
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun c v w h => ?_, ?_⟩
  · rw [mem_fixV_zpowers_iff_apply] at hv ⊢
    rw [happ, hv]
  · rw [commV_sig_eq hK, MonoidHom.mem_range] at hv ⊢
    obtain ⟨W, rfl⟩ := hv
    refine ⟨g W, ?_⟩
    rw [sigPsi_apply, sigPsi_apply, map_mul, map_inv, happ]
  · obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hL
    exact rho_smul_compat hK γ h
  · exact MonoidHom.mem_range.mp ((mem_range_rhoF_iff hn hK g).2 ⟨hL, hC⟩)

theorem nfs_sig_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))))
      (commV (Subgroup.zpowers (sig n K))) ⊥ 3 := by
  obtain ⟨β, hβs, hβk, hβc⟩ := sec_comm hn hK
  refine nfs_of_data (scalF n K) bar_scalF bot_le ?_ ?_ ?_ ?_ β hβs hβk hβc ?_ ?_
  · intro g hg v hv
    exact (sigG_facts hn hK hg).2.1 v hv
  · intro g _ v hv
    rw [Subgroup.mem_bot] at hv ⊢
    rw [hv, map_one]
  · intro c v w hv h
    exact smul_mem_commV_sig hn hK hv h
  · intro c v w hv h
    exact smul_mem_bot hv h
  · intro g hg c v w h
    exact (sigG_facts hn hK hg).2.2.1 c v w h
  · intro g hg hgu
    obtain ⟨h, rfl⟩ := (sigG_facts hn hK hg).2.2.2
    have hfix : ∀ u ∈ commV (Subgroup.zpowers (sig n K)), rhoF hK h u = u := fun u hu =>
      mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hgu u hu))
    rw [faith_comm hn hK hfix, map_one]

theorem nfs_sig_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))))
      (fixV (Subgroup.zpowers (sig n K))) (commV (Subgroup.zpowers (sig n K))) 3 := by
  obtain ⟨β, hβs, hβk, hβc⟩ := sec_fix hn hK
  refine nfs_of_data (scalF n K) bar_scalF
    (fun v hv => (mem_fixV_sig hK).2 ((mem_commV_sig hn hK).1 hv).2) ?_ ?_ ?_ ?_ β hβs hβk hβc
    ?_ ?_
  · intro g hg v hv
    exact (sigG_facts hn hK hg).1 v hv
  · intro g hg v hv
    exact (sigG_facts hn hK hg).2.1 v hv
  · intro c v w hv h
    exact smul_mem_fixV_sig hK hv h
  · intro c v w hv h
    exact smul_mem_commV_sig hn hK hv h
  · intro g hg c v w h
    exact (sigG_facts hn hK hg).2.2.1 c v w h
  · intro g hg hgu
    obtain ⟨h, rfl⟩ := (sigG_facts hn hK hg).2.2.2
    rw [faith_fix hn hK hgu, map_one]

theorem nfs_sig_top (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))))
      ⊤ (fixV (Subgroup.zpowers (sig n K))) 3 := by
  obtain ⟨β, hβs, hβk, hβc⟩ := sec_top hn hK
  refine nfs_of_data (scalF n K) bar_scalF le_top ?_ ?_ ?_ ?_ β hβs hβk hβc ?_ ?_
  · intro g _ v _
    exact Subgroup.mem_top _
  · intro g hg v hv
    exact (sigG_facts hn hK hg).1 v hv
  · intro c v w _ _
    exact Subgroup.mem_top _
  · intro c v w hv h
    exact smul_mem_fixV_sig hK hv h
  · intro g hg c v w h
    exact (sigG_facts hn hK hg).2.2.1 c v w h
  · intro g hg hgu
    obtain ⟨h, rfl⟩ := (sigG_facts hn hK hg).2.2.2
    rw [faith_top hn hK (fun u => hgu u (Subgroup.mem_top u)), map_one]

end CFSG.Quasithin.RonanH44
