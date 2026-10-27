module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434CharThreeL2Tools
import CFSG.RankThree.PartTwo.Sec5.Tools
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res4

open CFSG Matrix
open CFSG.GorensteinWalter (PSL2 PGL2 PGammaL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (pglAction semilinearAction
  semilinearEquivAut)
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Item434CharThree

theorem exists_conj_mem_of_elemAbelian {e : ℕ} (he : e ≠ 0)
    {E : Subgroup (MulAut (PSL2 (GaloisField 3 e)))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (h9 : 9 ≤ Nat.card E) :
    ∃ x : PSL2 (GaloisField 3 e), x ≠ 1 ∧ MulAut.conj x ∈ E ∧
      CFSG.Assembly.IsElemAbelian 3
        (Subgroup.centralizer ({x} : Set (PSL2 (GaloisField 3 e)))) ∧
      Nat.card (Subgroup.centralizer ({x} : Set (PSL2 (GaloisField 3 e)))) = 3 ^ e := by
  set K := GaloisField 3 e with hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKc : Nat.card K = 3 ^ e := GaloisField.card 3 e he
  set S := semilinearEquivAut K with hS
  set E' : Subgroup (PGammaL2 K) := E.comap S.toMonoidHom with hE'
  have hE'map : E'.map S.toMonoidHom = E := Subgroup.map_comap_eq_self_of_surjective S.surjective E
  have hE'card : Nat.card E' = Nat.card E := by
    rw [← hE'map, Subgroup.card_map_of_injective (f := S.toMonoidHom) S.injective]
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    Item434Kit.isElemAbelian_of_map_injective S.injective (hE'map ▸ hE)
  set ρ : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom with hρ
  have hcyc : IsCyclic (K ≃+* K) :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three K hKc).2
  have hρ3 : Nat.card (E'.map ρ) ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x : E'.map ρ ↦ ?_
    obtain ⟨_, y, hy, rfl⟩ := x
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hE'e.2 y hy, map_one]
  have h3 : 3 ≤ Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) := by
    have hcardE := Item434Alt.card_eq_card_inf_ker_mul_card_map ρ E'
    have hd := Nat.le_of_dvd (by norm_num) hρ3
    rw [hE'card] at hcardE
    by_contra hlt
    push Not at hlt
    have : Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) * Nat.card (E'.map ρ) ≤ 2 * 3 :=
      Nat.mul_le_mul (by omega) hd
    omega
  set P : Subgroup (PGL2 K) := (E' ⊓ ρ.ker).comap SemidirectProduct.inl with hP
  have hPmap : P.map SemidirectProduct.inl = E' ⊓ ρ.ker := by
    apply Subgroup.map_comap_eq_self
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact inf_le_right
  have hPcard : Nat.card P = Nat.card (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) := by
    rw [← hPmap, Subgroup.card_map_of_injective SemidirectProduct.inl_injective]
  have hPp : IsPGroup 3 P := by
    have h1 : IsPGroup 3 (E' ⊓ ρ.ker : Subgroup (PGammaL2 K)) :=
      (Sec5.isPGroup_of_isElemAbelian hE'e).to_le inf_le_left
    exact h1.comap_of_injective _ SemidirectProduct.inl_injective
  have : Finite (PGL2 K) := finite_pgl2
  obtain ⟨h, hh⟩ := Item434AltPerm.exists_le_map_conj_of_card (P₀ := unipPGL K)
    (by rw [card_unipPGL_galois he, factorization_card_pgl2 he]) hPp
  obtain ⟨g, hgP, hg1⟩ : ∃ g ∈ P, g ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr hno
    rw [hbot, Subgroup.card_bot] at hPcard
    omega
  set W := (unipPGL K).map (MulAut.conj h).toMonoidHom with hW
  have hgW : g ∈ W := hh hgP
  obtain ⟨x, hx⟩ := map_conj_unipPGL_le_range h hgW
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hg1
    rw [← hx, map_one]
  have hconj : MulAut.conj x ∈ E := by
    have hg' : S (SemidirectProduct.inl g) ∈ E := hgP.1
    rwa [show S (SemidirectProduct.inl g) = pglAction K g from
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl K g, ← hx,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL] at hg'
  set π := ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K) with hπ
  have hπinj : Function.Injective π := ProjectiveSpecialLinearGroup.toPGL_injective
  have hcent : Subgroup.centralizer ({x} : Set (PSL2 K)) = W.comap π := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap]
    constructor
    · intro hy
      apply mem_map_conj_unipPGL_of_commute hgW hg1
      rw [← hx, ← map_mul, ← map_mul, hy]
    · intro hy
      apply hπinj
      rw [map_mul, map_mul, hx]
      exact map_conj_unipPGL_commute hy hgW
  have hWrange : W ≤ π.range := map_conj_unipPGL_le_range h
  have hWmap : (W.comap π).map π = W := Subgroup.map_comap_eq_self hWrange
  refine ⟨x, hx1, hconj, ?_, ?_⟩
  · rw [hcent]
    refine Item434Kit.isElemAbelian_of_map_injective hπinj ?_
    rw [hWmap]
    refine ⟨⟨⟨fun a b => Subtype.ext (map_conj_unipPGL_commute a.2 b.2)⟩⟩, fun w hw => ?_⟩
    exact pow_three_eq_one_of_mem_map_conj hw
  · rw [hcent, ← Subgroup.card_map_of_injective hπinj, hWmap, hW,
      Subgroup.card_map_of_injective (MulAut.conj h).injective, card_unipPGL_galois he]

end CFSG.RankThree.PartTwo.Sec6.Res611Res4
