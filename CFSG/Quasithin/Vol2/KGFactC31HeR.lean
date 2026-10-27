module

public import CFSG.Quasithin.Vol2.KGFactC31HeSet
public import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Quasithin.Vol2.KGFactC31EBasis
public import CFSG.Quasithin.Vol2.KGFactC31Rad

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

variable {A : Type} [Group A] [Finite A] {S M₀ R M V : Subgroup A}
  {ι : A →* Equiv.Perm (Fin 8330)}

omit [Finite A] in
theorem cent_eq_of_ref (h : Setup S M₀ R M V) (hι : Emb S ι) {k l : ℕ}
    {v : Fin k → Equiv.Perm (Fin 8330)} {u : Fin l → Equiv.Perm (Fin 8330)} (hu : EBasis u)
    (hcent : ∀ x ∈ heAutGroup, (∀ i, x * v i = v i * x) → x ∈ eSub hu)
    (hvV : ∀ i, v i ∈ V.map ι) :
    Subgroup.centralizer (V : Set A) = (eSub hu).comap ι := by
  have hle : Subgroup.centralizer (V : Set A) ≤ (eSub hu).comap ι := by
    intro x hx
    refine hcent _ (hι.mem_heAutGroup x) fun i => ?_
    obtain ⟨v', hv', hvi⟩ := hvV i
    rw [← hvi, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx v' hv']
  refine le_antisymm hle fun z hz => Subgroup.mem_centralizer_iff.mpr fun v' hv' => ?_
  have hv'E := hle (h.V_le_cent hv')
  apply hι.inj
  rw [map_mul, map_mul]
  exact eSub_comm hu _ _ hv'E hz

theorem R_eq_of_ref (h : Setup S M₀ R M V) (hι : Emb S ι) {k l : ℕ}
    {v : Fin k → Equiv.Perm (Fin 8330)} {u : Fin l → Equiv.Perm (Fin 8330)} (hu : EBasis u)
    (huP : ∀ x ∈ eSub hu, x ∈ heP)
    (hcent : ∀ x ∈ heAutGroup, (∀ i, x * v i = v i * x) → x ∈ eSub hu)
    (hvV : ∀ i, v i ∈ V.map ι) : R = (eSub hu).comap ι := by
  have hC := cent_eq_of_ref h hι hu hcent hvV
  have hcard : Nat.card ((eSub hu).comap ι) = 2 ^ l := by
    rw [hι.card_comap huP, card_eSub]
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
    rw [hC]
    exact IsPGroup.of_card hcard
  rw [eq_centralizer_of_isPGroup h.hMN h.hM₀V h.hsyl h.hNR h.hRC h2, hC]

end CFSG.Quasithin.KGC31.He

end
