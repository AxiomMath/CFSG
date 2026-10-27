module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k : ℕ}

theorem pCoreOf_le_centralizerSection (hLM : L ≤ M) :
    pCoreOf 2 L ≤ centralizerSection M L (pCoreOf 2 L) := by
  intro o ho
  have hoL : o ∈ L := pCoreOf_le 2 L ho
  refine ⟨hLM hoL, Subgroup.le_normalizer hoL, le_normalizer_pCoreOf 2 L hoL, fun x hx => ?_⟩
  have h1 : x * o * x⁻¹ ∈ pCoreOf 2 L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L hx) o).mp ho
  exact (pCoreOf 2 L).mul_mem h1 ((pCoreOf 2 L).inv_mem ho)

theorem I_factorization_aux (hd : NoSumBigData G T M L Mm I H K m k)
    (hM : ∀ y ∈ M, ∃ l ∈ L, l⁻¹ * y ∈ centralizerSection M L (pCoreOf 2 L)) :
    ∀ y ∈ I, ∃ l ∈ I ⊓ L, ∃ c ∈ I ⊓ centralizerSection M L (pCoreOf 2 L), y = l * c := by
  intro y hy
  have hc : Conf4212 G T M L I H K := hd.2.2.1
  have hIM : I ≤ M := hc.I_le
  have hLM : L ≤ M := hc.hyp421.L_le
  obtain ⟨l, hl, hc₀⟩ := hM y (hIM hy)
  have hiota := hd.1.gammaStar.1.1
  have hLIO : L ≤ I ⊔ pCoreOf 2 L := by
    have h3 := hiota.2.2.1
    rwa [hc.conjClosure_eq] at h3
  have hIO : I ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (hIM.trans hc.normal).trans (normalizer_le_normalizer_pCoreOf 2 L)
  obtain ⟨i, hi, o, ho, rfl⟩ := (mem_sup_of_le_normalizer hIO).mp (hLIO hl)
  have hiL : i ∈ L := by
    have := L.mul_mem hl (L.inv_mem (pCoreOf_le 2 L ho))
    simpa using this
  have hoC : o ∈ centralizerSection M L (pCoreOf 2 L) := pCoreOf_le_centralizerSection hLM ho
  refine ⟨i, ⟨hi, hiL⟩, o * (i * o)⁻¹ * y, ⟨?_, ?_⟩, ?_⟩
  · have e : o * (i * o)⁻¹ * y = i⁻¹ * y := by group
    rw [e]
    exact I.mul_mem (I.inv_mem hi) hy
  · have := (centralizerSection M L (pCoreOf 2 L)).mul_mem hoC hc₀
    simpa [mul_assoc] using this
  · group

end CFSG.Quasithin.H13.Ch4.NSB
