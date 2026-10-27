module

public import Certificates.Kernel.BabyMonster.Three.Glue
public import Certificates.Kernel.BabyMonster.Three.Mem
public import Certificates.Kernel.BabyMonster.ZRk.Glue
public import CFSG.Certificates.Kernel.Common.RankCert
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KC.BM.ThreeCert

open CFSG.KC.BM CFSG.KC.BM.ThreeGlue CFSG.SectionRank.LocalWitness CFSG.Blueprint
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Solomon.Coordinator.B3B

local notation "sm" => stripMat

theorem rank_z : (sm Three.Z - 1).rank = 2916 := by
  have e : sm Three.Z - 1 = sm Three.Z + 1 := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply]
    exact CharTwo.sub_eq_add _ _
  obtain ⟨h1, h2, h3, h4⟩ := ZRkGlue.zRk_cert
  rw [e]
  exact CFSG.KC.RankCert.rank_of_cert (by norm_num) h1 h2 h3 h4

variable {S : Submonoid Mt}

theorem nf_of_mem (hT : sm Three.t79 ∈ S) (hH : sm Three.t58 ∈ S) :
    ∃ (x y : Fin 4 → Sˣ) (z : Sˣ) (g : Fin 2 → Sˣ),
      HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * x j * (g k)⁻¹ = nfProd x y z (nfXData.getD (4 * k.val + j.val) [])) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * y j * (g k)⁻¹ = nfProd x y z (nfYData.getD (4 * k.val + j.val) [])) ∧
      (∀ k : Fin 2, g k * z * (g k)⁻¹ = z ^ 2) ∧ Matrix.rank (z.val.val - 1) = 2916 := by
  have hz : (qq hT hH 8).val.val = sm Three.Z := vq hT hH 8
  exact ⟨xs hT hH, ys hT hH, qq hT hH 8, gs hT hH, heisCfg hT hH, ys_pow hT hH, actX hT hH,
    actY hT hH, actZ hT hH, by rw [hz]; exact rank_z⟩

abbrev SB := NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2

theorem cert36920_of_seeds (hA1 : sm Seeds.A1 ∈ SB) (hA2 : sm Seeds.A2 ∈ SB) :
    ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B) (g : Fin 2 → NativeSporadic.B),
      HeisCfg 3 4 x y z ∧ (∀ i, y i ^ 3 = 1) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * x j * (g k)⁻¹ = nfProd x y z (nfXData.getD (4 * k.val + j.val) [])) ∧
      (∀ (k : Fin 2) (j : Fin 4),
        g k * y j * (g k)⁻¹ = nfProd x y z (nfYData.getD (4 * k.val + j.val) [])) ∧
      (∀ k : Fin 2, g k * z * (g k)⁻¹ = z ^ 2) ∧ Matrix.rank (z.val.val - 1) = 2916 :=
  nf_of_mem (ThreeMem.three_mem hA1 hA2).1 (ThreeMem.three_mem hA1 hA2).2

theorem cert129021_of_seeds (hA1 : sm Seeds.A1 ∈ SB) (hA2 : sm Seeds.A2 ∈ SB) :
    ∃ (x y : Fin 4 → NativeSporadic.B) (z : NativeSporadic.B),
      HeisCfg 3 4 x y z ∧ ∀ i, y i ^ 3 = 1 := by
  obtain ⟨x, y, z, _, h, hy, _⟩ := cert36920_of_seeds hA1 hA2
  exact ⟨x, y, z, h, hy⟩

end CFSG.KC.BM.ThreeCert

end
