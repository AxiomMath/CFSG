module

public import CFSG.Quasithin.Vol2.Asc94.HeJ5
public import CFSG.Quasithin.Vol2.Asc94.HeM2

public section

namespace CFSG.Quasithin.A94.HeJ

open Subgroup CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem J_eq_tr : (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) = tr e L52.Jm :=
  (tr_sup e _ _).symm

theorem card_J : Nat.card ↥(tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) = 256 := by
  rw [J_eq_tr, card_tr, L52.card_Jm]; norm_num

theorem norm_J (hF6 : L52.F6Model) (hz : orderOf z = 2) :
    ∀ n ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G),
      (∀ x ∈ tr e L52.A1, n * x * n⁻¹ ∈ tr e L52.A1) ∧
        (∀ x ∈ tr e L52.A2, n * x * n⁻¹ ∈ tr e L52.A2) := by
  intro n hn
  obtain ⟨hnA, hnA'⟩ := (frame2 e hz hF6).normalizer_J_le hn
  exact ⟨fun x hx => (mem_normalizer_iff.mp hnA x).mp hx,
    fun x hx => (mem_normalizer_iff.mp hnA' x).mp hx⟩

theorem ndata (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) :
    NData (A := tr e L52.A1) (A' := tr e L52.A2) (uG e) (wG e)
      (normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (tr e L52.Tm) := by
  have hz := S.ord
  have hF := frame2 e hz hF6
  have hnorm := norm_J e hF6 hz
  have hcomm : ∀ {X : Subgroup L52.Hc}, IsElemAbelian 2 X → ∀ a ∈ tr e X, ∀ b ∈ tr e X,
      a * b = b * a := by
    intro X hX a ha b hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hX.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  refine
    { norm := hnorm
      JN := le_normalizer
      Aab := hcomm L52.isElemAbelian_A1
      A'ab := hcomm L52.isElemAbelian_A2
      Asq := ?_
      cent := ?_
      TN := HeK.isSylowOf_T_normalizer_J e hF6 S h1 h2
      Tf := ?_
      card := ?_ }
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_mul, ← sq, L52.isElemAbelian_A1.2 x' hx', map_one]
  · intro x hx
    have hzA : z ∈ tr e L52.A1 := by
      have := emb_mem_tr e L52.zt_mem_A1
      rwa [emb_zt e hz] at this
    have hzJ : z ∈ (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) :=
      (le_sup_left : tr e L52.A1 ≤ tr e L52.A1 ⊔ tr e L52.A2) hzA
    have hxC : x ∈ Cz z := mem_centralizer_singleton_iff.2 (hx z hzJ)
    obtain ⟨y, rfl⟩ := exists_emb e hxC
    have hy : y ∈ Subgroup.centralizer (L52.Jm : Set L52.Hc) := by
      rw [mem_centralizer_iff]
      intro w hw
      have hwJ : emb e w ∈ (tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) := by
        rw [J_eq_tr]; exact emb_mem_tr e hw
      exact (emb_mul_comm e).1 (hx _ hwJ).symm
    rw [L52.centralizer_Jm] at hy
    rw [← tr_inf]
    exact emb_mem_tr e hy
  · intro t ht h1' h2'
    obtain ⟨t', ht', rfl⟩ := ht
    rw [J_eq_tr]
    refine emb_mem_tr e (L52.mem_Jm_of_coords ht' (fun u hu => ?_) (fun w hw => ?_))
    · have := h1' (emb e u) (emb_mem_tr e hu)
      rwa [show emb e t' * emb e u * (emb e t')⁻¹ = emb e (t' * u * t'⁻¹) by simp [map_mul, map_inv],
        uG_emb, uG_emb] at this
    · have := h2' (emb e w) (emb_mem_tr e hw)
      rwa [show emb e t' * emb e w * (emb e t')⁻¹ = emb e (t' * w * t'⁻¹) by simp [map_mul, map_inv],
        wG_emb, wG_emb] at this
  · obtain ⟨-, hN, -⟩ := caseII_facts hF6 S h1 h2
    have hN' : Nat.card ↥(normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) =
        9 * 1024 := hN
    rw [hN', card_J]

end CFSG.Quasithin.A94.HeJ
