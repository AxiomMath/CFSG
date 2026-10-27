module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Sd
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3WrNorm
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Hyp

public section

namespace CFSG.Quasithin.E2P.Asc80

open CFSG.Quasithin.A312U3 CFSG.Assembly.LowTwoRank CFSG.Quasithin.B6 CFSG.QuasithinUnique

variable {p : ℕ} [Fact p.Prime]

theorem exists_noncomm_psu3 {F : Type} [Field F] [Finite F] (hp2 : p ≠ 2)
    (hF : Nat.card F = p ^ 2) : ∃ a b : PSU3F p F, a * b ≠ b * a :=
  ⟨piU p F (flipU hF), zcU hF, fun h => flipU_not_mem_leviU hp2 hF (by
    have h1 : flipU hF ∈ (leviCU hF).comap (piU p F) := mem_leviCU_of_commute_z hp2 hF h
    rwa [comap_leviCU hp2 hF] at h1)⟩

theorem asc80U3 (hirr : SU3OddIrr) (hp2 : p ≠ 2) {H : Type} [Group H] [Finite H]
    {K T M : Subgroup H} (hK : K.Normal) (hs : IsSimpleGroup ↥K) (hmodel : IsPSU 3 p 1 ↥K)
    (hc : Subgroup.centralizer (K : Set H) = ⊥) (hT : IsSylowTwoOf T ⊤) (hsup : K ⊔ T = ⊤)
    (hM : IsUniqueMaxOver ⊤ T M) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set H) ∧ p % 4 = 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_equiv_psu3 hmodel
  have hnabC := exists_noncomm_psu3 (p := p) (F := F) hp2 hF
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabC
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hX := asHyp_of_uniqueMax hK hs hnab hc hT hsup hM
  have h3 : p = 3 → ∀ {Y : Subgroup (SU3F p F)}, leviU hF ≤ Y → Odd Y.index →
      IsIrrIn (StatedSU 3 (p ^ 1) F) Y → ¬ Group.IsSolvable ↥Y :=
    fun hp3 _ hB _ hirr' => no_solvable_irreducible_u3_three hp3 hF hB hirr'
  have hMK := inf_M_eq_of_u3 hirr hp2 hF h3 hX e
  refine ⟨hMK, ?_⟩
  by_contra hp4
  have hodd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left hp2
  have hp34 : p % 4 = 3 := by omega
  obtain ⟨U, hU, hUB, hbot, hcomm, hnot⟩ := exists_wreathed_normalizer_u hp34 hF
  have : IsSimpleGroup ↥K := hs
  have : IsSimpleGroup (PSU3F p F) := e.symm.isSimpleGroup
  have hN := normalizer_centralizer_ne_top hnabC hbot hcomm
  have hle := hX.normalizer_centralizer_commutator_le_levi e hU hN hMK
  rw [centralizer_zOf_eq_leviCU hp2 hF hU hUB] at hle
  exact hnot hle

end CFSG.Quasithin.E2P.Asc80
