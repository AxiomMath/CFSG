module

public import CFSG.Quasithin.Vol2.Asc94.HeJ4
public import CFSG.Quasithin.Vol2.Asc94.HeJ6
public import CFSG.Quasithin.Vol2.Asc94.TSCaseII

public section

namespace CFSG.Quasithin.A94.HeJ

open Matrix Subgroup CFSG.CGT.M24S CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G} (e : ↥(Cz z) ≃* L52.Hc)

theorem mG_z (hz : orderOf z = 2) : mG e z = L52.zC L52.zt := by
  have h := mG_emb e L52.zt
  rwa [emb_zt e hz] at h

theorem det_mG_z (hz : orderOf z = 2) : (mG e z).det = 0 := by
  rw [mG_z e hz]
  exact L52.det_zC_zt

theorem exists_a : ∃ a : G, a ∈ tr e L52.A1 ⊓ tr e L52.A2 ∧ mG e a = 1 := by
  obtain ⟨x, hx, hxm⟩ := L52.exists_zC 1
  refine ⟨emb e x, ?_, by rw [mG_emb, hxm]⟩
  rw [← tr_inf]
  exact emb_mem_tr e hx

theorem not_inZG_of_mG_one (hF6 : L52.F6Model) (hz : orderOf z = 2) {a : G}
    (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : mG e a = 1) : ¬ InZG z a := by
  rintro ⟨g, hg⟩
  obtain ⟨n, hn, hna⟩ := (frame4 e hz hF6).fusion_B (a := z) (b := a)
    (frame4 e hz hF6).z_mem_B ha hg.symm
  have hzB : z ∈ tr e L52.A1 ⊓ tr e L52.A2 := (frame4 e hz hF6).z_mem_B
  have hnN : n⁻¹ ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G) :=
    inv_mem hn
  have hm := (tdata e).m_conj _ (norm_J e hF6 hz) ⟨n⁻¹, hnN⟩ hzB
  rw [show ((⟨n⁻¹, hnN⟩ : normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) : G) =
    n⁻¹ from rfl, inv_inv] at hm
  obtain ⟨P, Q, hPQ⟩ : ∃ P Q : M2, mG e (n⁻¹ * z * n) = P * mG e z * Qᵀ := ⟨_, _, hm⟩
  rw [hna, ham] at hPQ
  have hdet := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_mG_z e hz, mul_zero, zero_mul,
    Matrix.det_one] at hdet
  exact absurd hdet (by decide)

theorem card_NA (hz : orderOf z = 2) :
    Nat.card ↥(Cz z ⊓ normalizer (tr e L52.A1 : Set G)) = 3072 := by
  have : Cz z ⊓ normalizer (tr e L52.A1 : Set G) = tr e L52.NH1 := by
    ext x
    constructor
    · rintro ⟨hxz, hxn⟩
      obtain ⟨x', rfl⟩ := exists_emb e hxz
      exact emb_mem_tr e (by rw [← L52.normalizer_A1_eq]; exact (emb_mem_normalizer_tr e).1 hxn)
    · rintro ⟨x', hx', rfl⟩
      exact ⟨emb_mem_Cz e x', (emb_mem_normalizer_tr e).2 (by rw [L52.normalizer_A1_eq]; exact hx')⟩
  rw [this, card_tr, L52.card_NH1]

theorem card_M (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) :
    Nat.card ↥(normalizer (tr e L52.A1 : Set G)) = 138240 := by
  have hz := S.ord
  have h := Frame2.card_normalizer_A (frame2 e hz hF6)
  obtain ⟨-, -, h45, -⟩ := caseII_facts hF6 S h1 h2
  have hSz : (frame2 e hz hF6).Sz.ncard = 45 := h45
  have hNA : Nat.card ↥(frame2 e hz hF6).NA = 3072 := card_NA e hz
  have h' : Nat.card ↥(normalizer (tr e L52.A1 : Set G)) = (frame2 e hz hF6).Sz.ncard *
      Nat.card ↥(frame2 e hz hF6).NA := h
  rw [h', hSz, hNA]

theorem inZG_conj {a l : G} (h : InZG z (l⁻¹ * a * l)) : InZG z a := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g * l⁻¹, ?_⟩
  have : a = l * (l⁻¹ * a * l) * l⁻¹ := by group
  rw [this, hg]
  group

theorem card_Ω (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    {a : G} (ha : a ∈ tr e L52.A1) (ha1 : a ≠ 1) (hnz : ¬ InZG z a) :
    Nat.card {y : G // ∃ l ∈ normalizer (tr e L52.A1 : Set G), y = l⁻¹ * a * l} = 18 := by
  have hz := S.ord
  obtain ⟨-, -, -, -, hΩ, -⟩ := caseII_facts hF6 S h1 h2
  obtain ⟨hcard, htrans, -, -⟩ := hΩ
  have hmem : ∀ l ∈ normalizer (tr e L52.A1 : Set G), l⁻¹ * a * l ∈ (frame5 e hz hF6).Ω := by
    intro l hl
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (frame2 e hz hF6).conj_mem_A ha hl
    · intro h
      have h1' : l⁻¹ * a * l = 1 := h
      apply ha1
      have : a = l * (l⁻¹ * a * l) * l⁻¹ := by group
      rw [this, h1']
      group
    · rintro ⟨-, -, hZ⟩
      exact hnz (inZG_conj hZ)
  have haΩ : a ∈ (frame5 e hz hF6).Ω := by
    have := hmem 1 (one_mem _)
    simpa using this
  have hset : {y : G | ∃ l ∈ normalizer (tr e L52.A1 : Set G), y = l⁻¹ * a * l} =
      (frame5 e hz hF6).Ω := by
    ext y
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact hmem l hl
    · intro hy
      obtain ⟨n, hn, hyn⟩ := htrans a haΩ y hy
      exact ⟨n, hn, hyn⟩
  have h18 : Nat.card ↥((frame5 e hz hF6).Ω) = 18 := by
    rw [Nat.card_coe_set_eq]
    exact hcard
  rw [← h18, ← hset]
  rfl

theorem data40 (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    {a : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : mG e a = 1) :
    Data40 (tr e L52.A1) (tr e L52.A2) (uG e) (wG e) (mG e)
      (normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (tr e L52.Tm) a where
  hT := tdata e
  hK := ndata e hF6 S h1 h2
  ha := ha
  ham := ham
  cardJ := card_J e
  cardM := card_M e hF6 S h1 h2
  cardΩ := card_Ω e hF6 S h1 h2 ha.1
    (by rintro rfl; have := (tdata e).m_one; rw [ham] at this; exact one_ne_zero this)
    (not_inZG_of_mG_one e hF6 S.ord ha ham)

theorem data40_symm (hF6 : L52.F6Model) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    {a : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : mG e a = 1) :
    Data40 (tr e L52.A2) (tr e L52.A1) (wG e) (uG e) (fun x => (mG e x)ᵀ)
      (normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (tr e L52.Tm) a := by
  have hz := S.ord
  have ha1 : a ≠ 1 := by
    rintro rfl
    have := (tdata e).m_one
    rw [ham] at this
    exact one_ne_zero this
  have hnz := not_inZG_of_mG_one e hF6 hz ha ham
  have h1' : normalizer (tr (swapIso e) L52.U1 : Set G) = Cz z := by rw [tr_swap_U1]; exact h2
  have h2' : normalizer (tr (swapIso e) L52.U2 : Set G) = Cz z := by rw [tr_swap_U2]; exact h1
  have hM : Nat.card ↥(normalizer (tr e L52.A2 : Set G)) = 138240 := by
    have := card_M (swapIso e) hF6 S.swap h1' h2'
    rwa [tr_swap_A1] at this
  have hΩ : Nat.card {y : G // ∃ l ∈ normalizer (tr e L52.A2 : Set G), y = l⁻¹ * a * l} = 18 := by
    have := card_Ω (swapIso e) hF6 S.swap h1' h2' (a := a) (by rw [tr_swap_A1]; exact ha.2) ha1 hnz
    rwa [tr_swap_A1] at this
  refine (data40 e hF6 S h1 h2 ha ham).symm ?_ hM hΩ
  intro x hx
  obtain ⟨x', hx', rfl⟩ := hx
  rw [← map_mul, ← sq, L52.isElemAbelian_A2.2 x' hx', map_one]

end CFSG.Quasithin.A94.HeJ
