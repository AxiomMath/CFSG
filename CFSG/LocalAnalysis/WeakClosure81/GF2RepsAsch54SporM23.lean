module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporLat
public import CFSG.Quasithin.Background.E2TwoProofSporM23
public import Certificates.Certificate13
public import Certificates.Certificate14
public import Certificates.Certificate15
public import Certificates.Certificate16
public import Certificates.Certificate17
public import Certificates.Certificate18
public import Certificates.Certificate19
public import Certificates.Certificate20
public import Certificates.Certificate21
public import Certificates.Certificate22
public import Certificates.Certificate23
public import Certificates.Certificate24
public import Certificates.Certificate25
public import Certificates.Certificate26
public import Certificates.Certificate27
public import Certificates.Certificate28
public import Certificates.Certificate29
public import Certificates.Certificate30
public import Certificates.Certificate31
public import Certificates.Certificate32
public import Certificates.Certificate33
public import Certificates.Certificate34
public import Certificates.Certificate35
public import Certificates.Certificate36
public import Certificates.Certificate37
public import Certificates.Certificate38
public import Certificates.Certificate39
public import Certificates.Certificate40
public import Certificates.Certificate41
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate2196
public import Certificates.Certificate2197
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate4075
public import Certificates.Certificate7118
public import Certificates.Certificate7123
public import Certificates.Certificate8033
public import Certificates.Certificate9121
public import Certificates.Certificate9214

import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Schreier.M23

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat Subgroup
open CFSG.Quasithin.E2P.SporB CFSG.Quasithin.H.MathieuLat
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)


theorem asch54SporGenAt_m23 :
    Asch54SporGenAt .M23 := by
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hL : m23CtxB.D.Om.map (fun o => o.lbl.size) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9] := m23_lat_cert.2.2
  have hN : m23CtxB.D.O.lbl.size = 79695 := m23_lat_cert.2.1
  have hk : m23CtxB.k = 7 := rfl
  have hS : IsSylowTwoOf m23CtxB.S ⊤ := by
    refine K1.isSylowTwoOf_top_iff.mpr ⟨m23CtxB.S_isPGroup, ?_⟩
    have h1 := Subgroup.card_mul_index m23CtxB.S
    rw [m23CtxB.S_card, m23CtxB.hΓ, hN, hk] at h1
    have h2 : m23CtxB.S.index = 79695 := by omega
    rw [h2]
    norm_num
  have hall := lat_all m23CtxB hL
  have hcard := lat_card m23CtxB hL
  have hΓ : Nat.card ↥CFSG.Blueprint.NativeSporadic.M23 = 79695 * 2 ^ m23CtxB.k := by
    rw [m23CtxB.hΓ, hN]
  have hle : ∀ j jj : ℕ, j < 16 → jj < 16 → jj ∈ m23Incl[j]! → m23CtxB.Y j ≤ m23CtxB.Y jj :=
    fun _ _ hj hjj h => (m23_Y_le_iff hj hjj).mpr h
  have hnle : ∀ j jj : ℕ, j < 16 → jj < 16 → jj ∉ m23Incl[j]! →
      ¬ m23CtxB.Y j ≤ m23CtxB.Y jj :=
    fun _ _ hj hjj h h' => h ((m23_Y_le_iff hj hjj).mp h')
  have hOut : Nat.card (Outer ↥CFSG.Blueprint.NativeSporadic.M23) ≤ 2 :=
    CFSG.Sporadic.Schreier.at_m23_schreier.1
  have inv15 : ∀ ψ : MulAut ↥CFSG.Blueprint.NativeSporadic.M23,
      m23CtxB.S.map ψ.toMonoidHom = m23CtxB.S →
        (m23CtxB.Y 15).map ψ.toMonoidHom = m23CtxB.Y 15 :=
    fun ψ hψ => map_eq_of_unique_card (m23CtxB.S_le_Y 15) (fun Z hZ hZc =>
      (list_pair_of_card hall hcard hΓ (c := 15) (d := 15) (by decide) (by decide)
        (by decide +kernel) Z hZ hZc).elim id id) ψ hψ
  have inv5 : ∀ ψ : MulAut ↥CFSG.Blueprint.NativeSporadic.M23,
      m23CtxB.S.map ψ.toMonoidHom = m23CtxB.S →
        (m23CtxB.Y 5).map ψ.toMonoidHom = m23CtxB.Y 5 :=
    fun ψ hψ => map_eq_of_pair_of_invariant_le (m23CtxB.S_le_Y 5)
      (list_pair_of_card hall hcard hΓ (c := 5) (d := 2) (by decide) (by decide)
        (by decide +kernel)) (hle 15 5 (by norm_num) (by norm_num) (by decide))
      (hnle 15 2 (by norm_num) (by norm_num) (by decide)) ψ hψ (inv15 ψ hψ)
  refine asch54SporGenAt_of_isLPair_of_aut
    (CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv.map MulEquiv.symm)
    (fun X _ _ hX => (isCalL0_nonabelian_not_sectionalTwoRankLE X hX).1) hOut
    (T₀ := m23CtxB.S) hS
    ⟨m23CtxB.S_le_Y 8, m23CtxB.S_le_Y 9,
      fun h => hnle 1 8 (by norm_num) (by norm_num) (by decide) (le_top.trans h.symm.le),
      fun h => hnle 1 9 (by norm_num) (by norm_num) (by decide) (le_top.trans h.symm.le),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 7) (N := 5760) (by decide +kernel)
        (dvd_of_eq (by rw [hcard 8 (by decide), hk]; decide)),
      not_hasCompFactor_isCalL0_of_dvd hO (k := 7) (N := 1920) (by decide +kernel)
        (dvd_of_eq (by rw [hcard 9 (by decide), hk]; decide)),
      lat_sup_eq_top_of_not_le hall (m23CtxB.S_le_Y 8) fun j hj h1 h2 => by
        have hj16 : j < 16 := by simpa using hj
        exact (by decide : ∀ i < 16, i ∈ m23Incl[8]! → i ∉ m23Incl[9]!) j hj16
          ((m23_Y_le_iff (by norm_num) hj16).mp h1) ((m23_Y_le_iff (by norm_num) hj16).mp h2)⟩
    fun ψ hψ => ⟨map_eq_of_pair_of_invariant_le (m23CtxB.S_le_Y 8)
      (list_pair_of_card hall hcard hΓ (c := 8) (d := 3) (by decide) (by decide)
        (by decide +kernel)) (hle 15 8 (by norm_num) (by norm_num) (by decide))
      (hnle 15 3 (by norm_num) (by norm_num) (by decide)) ψ hψ (inv15 ψ hψ),
      map_eq_of_pair_of_le_invariant (m23CtxB.S_le_Y 9)
      (list_pair_of_card hall hcard hΓ (c := 9) (d := 7) (by decide) (by decide)
        (by decide +kernel)) (hle 9 5 (by norm_num) (by norm_num) (by decide))
      (hnle 7 5 (by norm_num) (by norm_num) (by decide)) ψ hψ (inv5 ψ hψ)⟩

end CFSG.LocalAnalysis.WeakClosure81

end
