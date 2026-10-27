module

public import CFSG.Quasithin.H13.LocDblRank
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate318001
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.HS.Native (hsData)

theorem hs_rank_check :
    CFSG.QuasithinUnique.Lin2.RankCert.ElemAbelianLt ↥(J hsData) 32 :=
  Certificates.certificate318001

theorem elemAbelianBound_HS_group :
    ElemAbelianBound ↥(J hsData) 16 := by
  intro E hE
  have hlt := hs_rank_check E hE
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.Open.IsElemAbelian.isPGroup hE)
  rw [hm] at hlt ⊢
  have h4 : m ≤ 4 := by
    by_contra h
    have h5 : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  calc 2 ^ m ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
    _ = 16 := by norm_num

theorem elemAbelianBound_HS :
    ElemAbelianBound CFSG.Blueprint.NativeSporadic.HS 16 := by
  have hF : Facts hsData 3 := CFSG.Sporadic.HS.hsFacts
  have h := elemAbelianBound_HS_group
  exact ElemAbelianBound.of_mulEquiv (A := ↥(J hsData)) (A' := CFSG.Blueprint.NativeSporadic.HS)
    (seedEquiv hF.toBaseFacts).symm h

end CFSG.Quasithin.H13.LocDbl
