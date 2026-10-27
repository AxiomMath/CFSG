module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompSpor
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Card
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFRank1Spor
public import CFSG.Quasithin.EmptyFaithful.S152He4Inv
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Certificates
open CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem NoTwoCentralNine.of_noInvCommNine {M : Type} [Group M] [Finite M]
    (h : He4.NoInvCommNine M) : NoTwoCentralNine M := by
  intro t ht _ h9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hE9, -, hEC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 2)
    Nat.prime_three (H := ⊥) (L := Subgroup.centralizer ({t} : Set M))
    (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact h9) bot_le
  have htt : t * t = 1 := by rw [← pow_two, ← ht]; exact pow_orderOf_eq_one t
  have ht1 := h E (by rw [hE9]; norm_num) t htt fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEC hp)
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem card_centralizer_subtype {G : Type*} [Group G] (H : Subgroup G) (t : H) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) = Nat.card (centralizerIn H (t : G)) := by
  rw [← map_centralizer_subtype, Subgroup.card_map_of_injective H.subtype_injective]

theorem m22_card_centralizerIn_involution
    {u : Equiv.Perm (Fin 22)}
    (hu : u ∈ NativeSporadic.M22) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M22 u) = 384 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_rep_data1
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m22Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok
  rw [← m22Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m22Certificate.originalSubgroup = 443520 := by
    rw [m22Certificate_originalSubgroup, m22_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz, hKc1, hcard]), hKc1]

theorem m23_card_centralizerIn_involution
    {u : Equiv.Perm (Fin 23)}
    (hu : u ∈ NativeSporadic.M23) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m23Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m23Rep1]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 4000 hok
  rw [← m23Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m23Certificate.originalSubgroup = 10200960 := by
    rw [m23Certificate_originalSubgroup, m23_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz, hKc1, hcard]), hKc1]

theorem m24_card_centralizerIn_involution
    {u : Equiv.Perm (Fin 24)}
    (hu : u ∈ NativeSporadic.M24) (ho : orderOf u = 2) :
    Nat.card (centralizerIn NativeSporadic.M24 u) = 7680 ∨
      Nat.card (centralizerIn NativeSporadic.M24 u) = 21504 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  rw [m24InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn m24Certificate hQ (pairTables_spec hn hA hB)
    1 (fun h hh => by simpa using hh) (by norm_num) [m24Rep1, m24Rep2]
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by simpa using hr1, hro1⟩
      · exact ⟨by simpa using hr2, hro2⟩) 40000 hok
  rw [← m24Certificate_originalSubgroup] at hu ⊢
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u (by simpa using hu) ho
  rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hcard : Nat.card m24Certificate.originalSubgroup = 244823040 := by
    rw [m24Certificate_originalSubgroup, m24_card]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [centralizerIn_eq_of_le _ _ hK1 (hsize _ (by simp)) (by rw [hsz.1, hKc1, hcard]), hKc1]
  · right
    rw [centralizerIn_eq_of_le _ _ hK2 (hsize _ (by simp)) (by rw [hsz.2, hKc2, hcard]), hKc2]

theorem noTwoCentralNine_m11 :
    NoTwoCentralNine ↥NativeSporadic.M11 :=
  NoTwoCentralNine.of_noInvCommNine (He4.noInvCommNine_m11 ⟨MulEquiv.refl _⟩)

theorem noTwoCentralNine_m12 :
    NoTwoCentralNine ↥NativeSporadic.M12 := by
  refine NoTwoCentralNine.of_cards m12_card [192, 240] (fun t ht => ?_) (by
    intro c hc i _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> omega)
  rw [card_centralizer_subtype]
  rcases m12_card_centralizerIn_involution t.2 (by rwa [Subgroup.orderOf_coe]) with h | h <;>
    simp [h]

theorem noTwoCentralNine_m22 :
    NoTwoCentralNine ↥NativeSporadic.M22 := by
  refine NoTwoCentralNine.of_cards m22_card [384] (fun t ht => ?_) (by
    intro c hc i _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    omega)
  rw [card_centralizer_subtype, m22_card_centralizerIn_involution t.2
    (by rwa [Subgroup.orderOf_coe])]
  simp

theorem noTwoCentralNine_m23 :
    NoTwoCentralNine ↥NativeSporadic.M23 := by
  refine NoTwoCentralNine.of_cards m23_card [2688] (fun t ht => ?_) (by
    intro c hc i _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    omega)
  rw [card_centralizer_subtype, m23_card_centralizerIn_involution t.2
    (by rwa [Subgroup.orderOf_coe])]
  simp

theorem noTwoCentralNine_m24 :
    NoTwoCentralNine ↥NativeSporadic.M24 := by
  refine NoTwoCentralNine.of_cards m24_card [7680, 21504] (fun t ht => ?_) (by
    intro c hc i _ _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> omega)
  rw [card_centralizer_subtype]
  rcases m24_card_centralizerIn_involution t.2 (by rwa [Subgroup.orderOf_coe]) with h | h <;>
    simp [h]

@[expose] def y12 : Equiv.Perm (Fin 12) :=
  m12gA * m12gB * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB⁻¹ * m12gA * m12gB⁻¹ * m12gA *
    m12gB⁻¹ * m12gA * m12gB⁻¹ * m12gA * m12gB * m12gA * m12gB * m12gA * m12gB * m12gA

theorem m12gB_pow_three : m12gB ^ 3 = 1 := by decide +kernel

theorem y12_pow_three : y12 ^ 3 = 1 := by decide +kernel

theorem m12gB_comm_y12 : m12gB * y12 = y12 * m12gB := by decide +kernel

theorem m12gB_ne_one : m12gB ≠ 1 := by decide +kernel

theorem y12_ne_one : y12 ≠ 1 := by decide +kernel

theorem y12_ne_m12gB : y12 ≠ m12gB := by decide +kernel

theorem y12_ne_m12gB_sq : y12 ≠ m12gB ^ 2 := by decide +kernel

theorem hasElemAb_nine_M12 :
    ∃ E : Subgroup ↥NativeSporadic.M12, IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  SBd19F.hasElemAb_nine_of_perm_pair m12b.2
    (m12a * m12b * m12a * m12b * m12a * m12b * m12a * m12b⁻¹ * m12a * m12b⁻¹ * m12a *
      m12b⁻¹ * m12a * m12b⁻¹ * m12a * m12b * m12a * m12b * m12a * m12b * m12a :
      NativeSporadic.M12).2
    m12gB_pow_three y12_pow_three m12gB_comm_y12 m12gB_ne_one y12_ne_one y12_ne_m12gB
    y12_ne_m12gB_sq

@[expose] def x24 : Equiv.Perm (Fin 24) :=
  m24gA * m24gB⁻¹ * m24gA * m24gB * m24gA * m24gB * m24gA

@[expose] def y24 : Equiv.Perm (Fin 24) :=
  m24gB * m24gA * m24gB⁻¹ * m24gA * m24gB⁻¹ * m24gA * m24gB * m24gA * m24gB⁻¹ * m24gA *
    m24gB⁻¹ * m24gA * m24gB⁻¹ * m24gA * m24gB * m24gA * m24gB * m24gA * m24gB⁻¹ * m24gA *
    m24gB⁻¹ * m24gA * m24gB * m24gA * m24gB⁻¹ * m24gA * m24gB * m24gA * m24gB⁻¹ * m24gA *
    m24gB

theorem x24_pow_three : x24 ^ 3 = 1 := by decide +kernel

theorem y24_pow_three : y24 ^ 3 = 1 := by decide +kernel

theorem x24_comm_y24 : x24 * y24 = y24 * x24 := by decide +kernel

theorem x24_ne_one : x24 ≠ 1 := by decide +kernel

theorem y24_ne_one : y24 ≠ 1 := by decide +kernel

theorem y24_ne_x24 : y24 ≠ x24 := by decide +kernel

theorem y24_ne_x24_sq : y24 ≠ x24 ^ 2 := by decide +kernel

theorem hasElemAb_nine_M24 :
    ∃ E : Subgroup ↥NativeSporadic.M24, IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  SBd19F.hasElemAb_nine_of_perm_pair
    (m24a * m24b⁻¹ * m24a * m24b * m24a * m24b * m24a : NativeSporadic.M24).2
    (m24b * m24a * m24b⁻¹ * m24a * m24b⁻¹ * m24a * m24b * m24a * m24b⁻¹ * m24a *
      m24b⁻¹ * m24a * m24b⁻¹ * m24a * m24b * m24a * m24b * m24a * m24b⁻¹ * m24a *
      m24b⁻¹ * m24a * m24b * m24a * m24b⁻¹ * m24a * m24b * m24a * m24b⁻¹ * m24a *
      m24b : NativeSporadic.M24).2
    x24_pow_three y24_pow_three x24_comm_y24 x24_ne_one y24_ne_one y24_ne_x24 y24_ne_x24_sq

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem Conf12626.not_m11
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .M11) : False := by
  let e' : ↥K ≃* ↥NativeSporadic.M11 := e
  exact h.false_of_noTwoCentralNine hQ e' m11_center_eq_bot'
    (not_three_dvd_card_outer_of_le m11_center_eq_bot'
      (m11_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))))
    SBd19F.hasElemAb_nine_M11 noTwoCentralNine_m11
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem Conf12626.not_m12
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .M12) : False := by
  let e' : ↥K ≃* ↥NativeSporadic.M12 := e
  exact h.false_of_noTwoCentralNine hQ e' m12_center_eq_bot'
    (not_three_dvd_card_outer_of_le m12_center_eq_bot' m12_mulAut_card)
    hasElemAb_nine_M12 noTwoCentralNine_m12
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem Conf12626.not_m22
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .M22) : False := by
  let e' : ↥K ≃* ↥NativeSporadic.M22 := e
  exact h.false_of_noTwoCentralNine hQ e' m22_center_eq_bot'
    (not_three_dvd_card_outer_of_le m22_center_eq_bot' m22_mulAut_card)
    Lin2.OddRank.Mat.hasElemAb_nine_M22 noTwoCentralNine_m22
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem Conf12626.not_m23
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .M23) : False := by
  let e' : ↥K ≃* ↥NativeSporadic.M23 := e
  exact h.false_of_noTwoCentralNine hQ e' m23_center_eq_bot'
    (not_three_dvd_card_outer_of_le m23_center_eq_bot'
      (m23_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))))
    Lin2.OddRank.Mat.hasElemAb_nine_M23 noTwoCentralNine_m23
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

theorem Conf12626.not_m24
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) (hS : Ch1.SporadicAutInner)
    (e : ↥K ≃* NativeSporadic.Carrier .M24) : False := by
  let e' : ↥K ≃* ↥NativeSporadic.M24 := e
  exact h.false_of_noTwoCentralNine hQ e' m24_center_eq_bot'
    (not_three_dvd_card_outer_of_le m24_center_eq_bot'
      (m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num))))
    hasElemAb_nine_M24 noTwoCentralNine_m24
    (isInnerAut_of_sporadicAutInner hQ hS (by simp [Ch1.IsSQTKSporadicName]) (by decide) e)

end CFSG.Quasithin.H13.S126C
