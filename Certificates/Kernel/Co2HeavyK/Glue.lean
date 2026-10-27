module

public import CFSG.Certificates.Kernel.Co2HeavyK.Group
public import CFSG.Certificates.Kernel.Co2HeavyK.M22
public import Certificates.Kernel.Co2HeavyK.Bind
public import Certificates.Kernel.Co2HeavyK.Chunks
public import Certificates.Kernel.Co2HeavyK.Part1
public import Certificates.Kernel.Co2HeavyK.Part2
public import Certificates.Kernel.Co2HeavyK.Wit
public import Certificates.Kernel.Co2HeavyK.M22
public import Certificates.Kernel.Co2HeavyK.Transp
public import Certificates.Kernel.Sporadic.Co2Inv.Recs
public import Certificates.Kernel.Sporadic.Co2Inv.Gens

set_option exponentiation.threshold 600

public section

namespace CertificateChecks.KernelCo2HeavyK

open CFSG.KC.Co2HeavyK CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KC.M1F2
  CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Heavy CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
  CFSG.KS.Prim CFSG.Certificates.Native CFSG.Blueprint CFSG.QuasithinUnique.Lin2.RankCert
  CertificateChecks.KernelSpor.Co2Inv

theorem rowCheck_of {X T PT PTi : ℕ} (ht : transposeRows 22 (unpackR 22 X) = unpackR 22 T)
    (hv : ∀ i < 2300, mvecK VP T PT i = true)
    (hp : invEqK 2300 12 (mask 12) (2300 * 12) PT PTi = true)
    (hh : Nat.beq (Nat.shiftRight PT (2300 * 12)) 0 = true)
    (hs : siftK 2300 12 (mask 12) (2300 * 12) (pidn 2300 12) KernelSpor.Co2A.LR
      KernelSpor.Co2A.TRI KernelSpor.Co2A.BP 6 0 PT = true) :
    rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable (unpackR 22 X) = true := by
  have hvec : ∀ i < 2300, pg 12 (mask 12) PT i < 2300 ∧
      vecMulN 22 (transposeRows 22 (unpackR 22 X)) co2PackedVecs[i]! =
        co2PackedVecs[pg 12 (mask 12) PT i]! := by
    intro i hi
    obtain ⟨hlt, he⟩ := mvec_sound (hv i hi)
    refine ⟨hlt, ?_⟩
    rw [ht, vecMulN_unpackR, vp_get hi, vp_get hlt, he]
  have hperm : rowPerm co2PosTable (unpackR 22 X) = unpack 2300 12 PT := by
    unfold rowPerm unpack
    change Array.ofFn (n := 2300) (fun i => (co2PosTable[vecMulN 22
        (transposeRows 22 (unpackR 22 X)) co2PackedVecs[i.val]!]!).toNat) =
      Array.ofFn (n := 2300) (fun i => pg 12 (mask 12) PT i.val)
    refine congrArg (Array.ofFn (n := 2300)) (funext fun i => ?_)
    obtain ⟨hlt, he⟩ := hvec i i.2
    rewrite [he]
    exact posTable_ok _ hlt
  obtain ⟨hinv, hisinv⟩ := invEqK_sound hp
  unfold rowCheck
  rewrite [hperm]
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨⟨wfRows_unpack _, unpack_size _ _ _⟩, by rewrite [hinv]; exact hisinv⟩,
    fun i hi => ?_⟩, ?_⟩
  · rewrite [unpack_get hi, (hvec i hi).2]
    exact rfl
  · exact siftK_soundR KernelSpor.Co2A.binds KernelSpor.Co2A.perm KernelSpor.Co2A.hl rfl
      (Nat.eq_of_beq_eq_true hh) (range_of_permOK hp) hs

theorem rowA : rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable
    (unpackR 22 (MT 0)) = true :=
  rowCheck_of ta_eq vecA permA hiA siftA

theorem rowB : rowCheck (rawLevels 2300 co2StrongArrs co2BaseArr) co2PosTable
    (unpackR 22 (MT 1)) = true :=
  rowCheck_of tb_eq vecB permB hiB siftB

theorem mt1_lt : MT 1 < 2 ^ 484 := by decide +kernel

theorem invA : mulRows 22 (unpackR 22 (MT 0)) (unpackR 22 (MT 2)) = idRows 22 := by
  rw [mulRows_unpack, (inv_sound inv_ok).1, ← idRows_eq]

theorem invB : mulRows 22 (unpackR 22 (MT 1)) (unpackR 22 (MT 3)) = idRows 22 := by
  rw [mulRows_unpack, (inv_sound inv_ok).2.1, ← idRows_eq]

theorem neB : unpackR 22 (MT 1) ≠ idRows 22 := by
  intro e
  rw [idRows_eq] at e
  exact (inv_sound inv_ok).2.2 (unpack_inj mt1_lt IDP_lt e)

theorem relAB : ∀ v ∈ TauCeti.SporadicName.M22.presentation.relatorLetters,
    wordRows (unpackR 22 (MT 0)) (unpackR 22 (MT 1)) (unpackR 22 (MT 2)) (unpackR 22 (MT 3)) v =
      idRows 22 := by
  intro v hv
  rw [m22RelsK_eq] at hv
  rw [wordRows_unpack, rel_sound rel_ok v hv, ← idRows_eq]

theorem normA : ∀ i, inL2K W i = true →
    ∃ m, inL2K W m = true ∧ mulV (MT 0) (SQ i) = mulV (SQ m) (MT 0) := by
  intro i hi
  obtain ⟨h1, h2, -, -⟩ := norm_sound (norm_all i (inL2K_iff.1 hi).1) hi
  exact ⟨_, h1, h2⟩

theorem normB : ∀ i, inL2K W i = true →
    ∃ m, inL2K W m = true ∧ mulV (MT 1) (SQ i) = mulV (SQ m) (MT 1) := by
  intro i hi
  obtain ⟨-, -, h1, h2⟩ := norm_sound (norm_all i (inL2K_iff.1 hi).1) hi
  exact ⟨_, h1, h2⟩

theorem elemAbelianLt_co2K :
    ElemAbelianLt NativeSporadic.Co2 (2 ^ 11) :=
  elemAbelianLt_of_K recsK bind_all chunk_all ca_ends part1_all part2_all wit_all l2_count

theorem co2_v0_m22K :
    ∃ V₀ H : Subgroup NativeSporadic.Co2,
      (∀ E : Subgroup NativeSporadic.Co2, CFSG.Open.IsElemAbelian 2 E → 2 ^ 10 ≤ Nat.card E →
        ∃ g : NativeSporadic.Co2, E.map (MulAut.conj g).toMonoidHom = V₀) ∧
      H ≤ Subgroup.normalizer (V₀ : Set NativeSporadic.Co2) ∧ IsSimpleGroup H ∧
        ¬ IsMulCommutative H ∧ Nat.card H = 443520 := by
  obtain ⟨H, hHN, hs, hnc, hcard⟩ := exists_m22_of_rows rowA rowB invA invB neB relAB
    (fun _ hx => conj_mem_gensK recsK bind_all normA hx)
    (fun _ hx => conj_mem_gensK recsK bind_all normB hx)
  exact ⟨v0K W, H, exists_conj_eq_v0K recsK bind_all chunk_all ca_ends part1_all part2_all
    wit_all l2_count, hHN, hs, hnc, hcard⟩

end CertificateChecks.KernelCo2HeavyK

end
