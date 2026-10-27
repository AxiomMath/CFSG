module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkModelDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutPerf
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutAb
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutLift

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.PSL2Table
open scoped Pointwise commutatorElement MatrixGroups

theorem autFactL2Block1521_of (hmodel : L2ModelFacts) : AutFactL2Block1521 := by
  intro G _ _ L P hshort hLn hP v hv hv2 hc
  obtain ⟨n, hn, hLn⟩ := hLn
  have hn2 : 2 ≤ n := hn
  have hLL : ⁅L, L⁆ = L := commutator_eq_self_of_isShort2_lin2_1521 hn2 hshort hLn
  obtain ⟨hnoq, hchar, ⟨hUQc, hU2⟩, hqs, ⟨hZU, hirr⟩⟩ := hshort
  obtain ⟨F, hF, hfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hLn
  have : Finite F := Finite.of_fintype F
  have hK : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hchar2 : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hmkinj : Function.Injective (mk : SL(2, F) →* PSL(2, F)) := mk_injective_of_charTwo1521
  let π : ↥L →* PSL(2, F) := (mk : SL(2, F) →* PSL(2, F)).comp α
  have hπ : Function.Surjective π := mk_surjective.comp hαs
  have hπα : ∀ x : ↥L, π x = mk (α x) := fun x => rfl
  have hkerπ : π.ker = CFSG.pCore 2 ↥L := by
    rw [← hαk]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hπα, ← map_one (mk : SL(2, F) →* PSL(2, F))]
    exact hmkinj.eq_iff
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 PSL(2, F) := (A4.toSylow hP).mapSurjective (f := π) hπ
  have hQ : (Q : Subgroup PSL(2, F)) = (P.subgroupOf L).map π := rfl
  obtain ⟨hrig0, hidx0, hfix0⟩ := hmodel F n hn2 hK Q
  rw [hQ] at hrig0 hidx0 hfix0
  have hA : ∀ l ∈ L, ⁅l, v⁆ ∈ blockQ L :=
    commutator_mem_pCoreOf_of_centralizes1521 hP hπ hkerπ hrig0 hv hc
  have hQL : blockQ L ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) := le_normalizer_pCoreOf 2 L
  have hvQ : v ∈ Subgroup.normalizer (blockQ L : Set G) := normalizer_le_normalizer_pCoreOf 2 L hv
  have hUc : ∀ x ∈ blockU L, ∀ q ∈ blockQ L, x * q = q * x := fun x hx q hq =>
    ((Subgroup.mem_centralizer_iff.mp (hUQc hx).2) q hq).symm
  have hUcomm : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := fun x hx y hy =>
    hUc x hx y (hUQc hy).1
  obtain ⟨hAU, hcentU, hC⟩ := block_centralizes_aux1521 (L := L) (Q := blockQ L) (U := blockU L)
    (Z := blockZ L) hLL hQL hLQ rfl hUc hU2 rfl hZU hirr hv hvQ hv2 hA
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ L) L
  have hvU : v ∈ Subgroup.normalizer (blockU L : Set G) := A4.mem_normalizer_commutator hvQ hv
  have hZmem : ∀ z, z ∈ blockZ L ↔ z ∈ blockU L ∧ ∀ l ∈ L, l * z = z * l := by
    intro z
    show z ∈ blockU L ⊓ Subgroup.centralizer (L : Set G) ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]; exact Iff.rfl
  have hZcent : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := by
    intro z hz l hl
    rw [(hZmem z).1 hz |>.2 l hl]; group
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    le_normalizer_of_forall_conj_mem1521 fun l hl z hz => by rw [hZcent z hz l hl]; exact hz
  have hUZ : blockU L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    le_normalizer_of_forall_conj_mem1521 fun u hu z hz => by
      have : u * z * u⁻¹ = z := by rw [hUcomm u hu z ((hZmem z).1 hz).1]; group
      rw [this]; exact hz
  have hvZ : v ∈ Subgroup.normalizer (blockZ L : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hvU, mem_normalizer_centralizer1521 hv⟩
  obtain ⟨H, hHL, hHidx, hHprop⟩ := exists_odd_index_oTwoUpper1521 hP hπ hkerπ hidx0
  have hδH : ∀ h ∈ H, ⁅h, v⁆ ∈ blockZ L := by
    intro h hh
    obtain ⟨b, hb, q, hq, rfl⟩ := hHprop h hh
    have hbL : b ∈ L := (oTwoUpper_le _ hb).1
    have hbv : ⁅b, v⁆ = 1 := by
      rw [commutatorElement_def, show b * v = v * b from (hc b hb).symm]; group
    have e : ⁅b * q, v⁆ = (b * ⁅q, v⁆ * b⁻¹) * ⁅b, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hbv, mul_one]
    exact (Subgroup.mem_normalizer_iff.mp (hLZ hbL) _).mp (hC q hq)
  obtain ⟨u, huU, hu⟩ := exists_twist_of_odd_index1521 hUcomm hU2 hLU hLZ hAU hHidx hδH
  have hZc : blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have huv : ∀ l ∈ L, (u * v) * l = l * (u * v) :=
    centralizes_of_commutator_mem_center1521 hLL hZc (Subgroup.mul_mem _ (hUZ huU) hvZ) hu
  have huB : ∀ b ∈ oTwoUpper (L ⊓ Subgroup.normalizer (P : Set G)), b * u = u * b := by
    intro b hb
    have hbL : b ∈ L := (oTwoUpper_le _ hb).1
    have h1 := huv b hbL
    have h2 : b * v⁻¹ = v⁻¹ * b := by
      have := hc b hb
      calc b * v⁻¹ = v⁻¹ * (v * b) * v⁻¹ := by group
        _ = v⁻¹ * (b * v) * v⁻¹ := by rw [this]
        _ = v⁻¹ * b := by group
    calc b * u = b * (u * v) * v⁻¹ := by group
      _ = (u * v) * b * v⁻¹ := by rw [← h1]
      _ = (u * v) * (b * v⁻¹) := by group
      _ = (u * v) * (v⁻¹ * b) := by rw [h2]
      _ = u * b := by group
  have huZ : u ∈ blockZ L := by
    have hfix : ∀ M : SL(2, F), mk M ∈ oTwoUpper (Subgroup.normalizer
        (((P.subgroupOf L).map π : Subgroup PSL(2, F)) : Set PSL(2, F))) →
        (M : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β ⟨u, huU⟩)) =
          Multiplicative.toAdd (β ⟨u, huU⟩) := by
      intro M hM
      obtain ⟨b, hb, hbM⟩ := exists_lift_oTwoUpper1521 hP hπ hkerπ hM
      have hαb : α b = M := hmkinj (by rw [← hπα]; exact hbM)
      have hbu := huB _ hb
      have := hβe b ⟨u, huU⟩ ⟨u, huU⟩ (by
        show u = (b : G) * u * (b : G)⁻¹
        rw [hbu]; group)
      rw [← hαb]
      exact this.symm
    have h0 := hfix0 _ hfix
    have : β ⟨u, huU⟩ = 1 := by
      rw [← toAdd_eq_zero]; exact h0
    have hker : (⟨u, huU⟩ : ↥(blockU L)) ∈ β.ker := MonoidHom.mem_ker.mpr this
    rw [hβk] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  intro l hl
  have h1 := huv l hl
  have h2 : l * u = u * l := (hZmem u).1 huZ |>.2 l hl
  have h3 : u * (v * l) = u * (l * v) := by
    calc u * (v * l) = (u * v) * l := by group
      _ = l * (u * v) := h1
      _ = (l * u) * v := by group
      _ = (u * l) * v := by rw [h2]
      _ = u * (l * v) := by group
  exact mul_left_cancel h3


end CFSG.Quasithin
