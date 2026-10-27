module

public import CFSG.Quasithin.EmptyFaithful.A38c11Case3
public import CFSG.Quasithin.EmptyFaithful.A38c16Check
public import CFSG.Quasithin.EmptyFaithful.A38c16Core
public import CFSG.Quasithin.EmptyFaithful.A38c16Aut
public import CFSG.Quasithin.EmptyFaithful.A38c16Act

public section

namespace CFSG.Quasithin.A38c16

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7

theorem case3Direct
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h56 : AsB56) (hD310 : D310)
    (hD391 : D391) (hNat : Insp14622Nat) : Case3Direct := by
  intro G _ _ T M S hB c19 c20 K hK Kp hKp hne hnK hnKp hper hL32 hL32p
  have hsumK := commutator_le_sum_natural h37 h38 h39 h56 hD310 hD391 hNat S hB c19 c20 hK hKp hne
    hnK hnKp hper hL32
  have hsumKp := commutator_le_sum_natural h37 h38 h39 h56 hD310 hD391 hNat S hB c19 c20 hKp hK
    hne.symm hnKp hnK (by rw [hper, sup_comm]) hL32p
  obtain ⟨W, _, _, hW, Γ, K', Kp', θ, θp, s, A, hΓ, hs, hso, hA, hAp, hAΓ, hA1, hAe, hAq, hfin⟩ :=
    case3_interface h37 h38 h39 S hB c19 c20 hK hKp hne hnK hnKp hper hL32 hL32p hsumK hsumKp
  exact hfin (case3_core hW sl3OutFacts case3Check hΓ θ θp hs hso hA hAp hAΓ hA1 hAe hAq)

end CFSG.Quasithin.A38c16
