module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2G

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H13
  CFSG.Quasithin.H13.L828T

section Transport

variable {V W : Type} [CommGroup V] [CommGroup W] [Finite V] [Finite W]

theorem commutant_iso_of_map (e : V ≃* W) (H X : Subgroup (MulAut V)) :
    Nonempty (↥(commutant (s828BPrime H X) (fixV X)
        ((perfectCore (H ⊓ stabSub (fixV X)) : Subgroup (MulAut V)) : Set (MulAut V))) ≃+*
      ↥(commutant (s828BPrime (H.map (congrHom e)) (X.map (congrHom e)))
        (fixV (X.map (congrHom e)))
        ((perfectCore (H.map (congrHom e) ⊓ stabSub (fixV (X.map (congrHom e)))) :
          Subgroup (MulAut W)) : Set (MulAut W)))) := by
  have := commutant_equiv_map_subgroup e (s828BPrime H X) (fixV X)
    (perfectCore (H ⊓ stabSub (fixV X)))
  rw [s828BPrime_map, ← fixV_map_congrHom, perfectCore_inf_stab_map] at this
  exact this

theorem mb2_iso_of_std (e : V ≃* W) (H X : Subgroup (MulAut V)) {Hs Xs : Subgroup (MulAut W)}
    (hH : H.map (congrHom e) = Hs) (hX : X.map (congrHom e) = Xs) {B U : Subgroup W}
    {P : Subgroup (MulAut W)} (hB : s828BPrime Hs Xs = B) (hU : fixV Xs = U)
    (hP : perfectCore (Hs ⊓ stabSub (fixV Xs)) = P) {K : Type} [Ring K]
    (hstd : Nonempty (↥(commutant B U (P : Set (MulAut W))) ≃+* K)) :
    Nonempty (↥(commutant (s828BPrime H X) (fixV X)
        ((perfectCore (H ⊓ stabSub (fixV X)) : Subgroup (MulAut V)) : Set (MulAut V))) ≃+* K) := by
  subst hH hX
  obtain ⟨i1⟩ := commutant_iso_of_map e H X
  subst hB hU hP
  obtain ⟨i2⟩ := hstd
  exact ⟨i1.trans i2⟩

end Transport

end CFSG.Quasithin.H13.Mat
