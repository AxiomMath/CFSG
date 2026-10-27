module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamBlkT
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamBlkQ
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutAb
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkAutPerf

public section

namespace CFSG.Quasithin.E9.Blk

open CFSG.Open CFSG.QuasithinUnique CFSG.PSL2Table CFSG.Quasithin CFSG.Quasithin.L21521
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem block_centralizes_of_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hshort : IsShort2 L) (hLL : ⁅L, L⁆ = L) {F : Type} [Field F] [Finite F]
    (hK : Nat.card F = 2 ^ n) (α : ↥L →* SL(2, F)) (hαs : Function.Surjective α)
    (hαk : α.ker = CFSG.pCore 2 ↥L) (β : blockU L →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ ℓ : ↥L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hP : IsSylowTwoOf P L) {b : ↥L}
    (hR : ∀ γ : MulAut PSL(2, F), (∀ x ∈ P.subgroupOf L, γ (mk (α x)) = mk (α x)) →
      γ (mk (α b)) = mk (α b) → γ = 1)
    {A : SL(2, F)} {a : Fˣ} (ha : (a : F) ≠ 1) (hαb : α b = A * diag a * A⁻¹) {v : G}
    (hv : v ∈ Subgroup.normalizer (L : Set G)) (hv2 : IsPGroup 2 ↥(Subgroup.zpowers v))
    (hcP : ∀ x ∈ P, v * x = x * v) (hcb : v * (b : G) = (b : G) * v) :
    ∀ l ∈ L, v * l = l * v := by
  obtain ⟨hnoq, hchar, ⟨hUQc, hU2⟩, hqs, ⟨hZU, hirr⟩⟩ := hshort
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
  have hA : ∀ l ∈ L, ⁅l, v⁆ ∈ blockQ L := by
    refine commutator_mem_pCoreOf_of_rigid hπ hkerπ hv fun γ hγ => hR γ (fun x hx => ?_) (hγ b hcb)
    exact hγ x (hcP x (Subgroup.mem_subgroupOf.mp hx))
  have hQL : blockQ L ≤ L := pCoreOf_le 2 L
  have hLQ : L ≤ Subgroup.normalizer (blockQ L : Set G) := le_normalizer_pCoreOf 2 L
  have hvQ : v ∈ Subgroup.normalizer (blockQ L : Set G) := normalizer_le_normalizer_pCoreOf 2 L hv
  have hUc : ∀ x ∈ blockU L, ∀ q ∈ blockQ L, x * q = q * x := fun x hx q hq =>
    ((Subgroup.mem_centralizer_iff.mp (hUQc hx).2) q hq).symm
  have hUcomm : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := fun x hx y hy =>
    hUc x hx y (hUQc hy).1
  obtain ⟨hAU, -, -⟩ := block_centralizes_aux1521 (L := L) (Q := blockQ L) (U := blockU L)
    (Z := blockZ L) hLL hQL hLQ rfl hUc hU2 rfl hZU hirr hv hvQ hv2 hA
  have hLU : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (blockQ L) L
  have hvU : v ∈ Subgroup.normalizer (blockU L : Set G) := A4.mem_normalizer_commutator hvQ hv
  have hZmem : ∀ z, z ∈ blockZ L ↔ z ∈ blockU L ∧ ∀ l ∈ L, l * z = z * l := by
    intro z
    show z ∈ blockU L ⊓ Subgroup.centralizer (L : Set G) ↔ _
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hZcent : ∀ z ∈ blockZ L, ∀ l ∈ L, l * z * l⁻¹ = z := by
    intro z hz l hl
    rw [(hZmem z).1 hz |>.2 l hl]
    group
  have hLZ : L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    le_normalizer_of_forall_conj_mem1521 fun l hl z hz => by rw [hZcent z hz l hl]; exact hz
  have hUZ : blockU L ≤ Subgroup.normalizer (blockZ L : Set G) :=
    le_normalizer_of_forall_conj_mem1521 fun u hu z hz => by
      have : u * z * u⁻¹ = z := by rw [hUcomm u hu z ((hZmem z).1 hz).1]; group
      rw [this]; exact hz
  have hvZ : v ∈ Subgroup.normalizer (blockZ L : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hvU, mem_normalizer_centralizer1521 hv⟩
  have hδP : ∀ h ∈ P, ⁅h, v⁆ ∈ blockZ L := by
    intro h hh
    have h1 : ⁅h, v⁆ = 1 := by
      rw [commutatorElement_def, show h * v = v * h from (hcP h hh).symm]
      group
    rw [h1]
    exact Subgroup.one_mem _
  obtain ⟨u, huU, hu⟩ := exists_twist_of_odd_index1521 hUcomm hU2 hLU hLZ hAU hP.2.2 hδP
  have hZc : blockZ L ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have huv : ∀ l ∈ L, (u * v) * l = l * (u * v) :=
    centralizes_of_commutator_mem_center1521 hLL hZc (Subgroup.mul_mem _ (hUZ huU) hvZ) hu
  have hub : (b : G) * u = u * (b : G) := by
    have h1 := huv b b.2
    have h2 : (b : G) * v⁻¹ = v⁻¹ * (b : G) := by
      calc (b : G) * v⁻¹ = v⁻¹ * (v * b) * v⁻¹ := by group
        _ = v⁻¹ * (b * v) * v⁻¹ := by rw [hcb]
        _ = v⁻¹ * b := by group
    calc (b : G) * u = b * (u * v) * v⁻¹ := by group
      _ = (u * v) * b * v⁻¹ := by rw [← h1]
      _ = (u * v) * (b * v⁻¹) := by group
      _ = (u * v) * (v⁻¹ * b) := by rw [h2]
      _ = u * b := by group
  have huZ : u ∈ blockZ L := mem_blockZ_of_commute α β hβk hβe ha hαb huU hub
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

theorem block_centerOf_of_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hLL : ⁅L, L⁆ = L) {F : Type} [Field F] [Finite F] (hK : Nat.card F = 2 ^ n)
    (α : ↥L →* SL(2, F)) (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (β : blockU L →* Multiplicative (Fin 2 → F))
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ ℓ : ↥L, ∀ u v : blockU L, (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    (hP : IsSylowTwoOf P L) {b : ↥L}
    (hC : ∀ x ∈ P.subgroupOf L, x * b = b * x → α x = 1)
    {A : SL(2, F)} {a : Fˣ} (ha : (a : F) ≠ 1) (hαb : α b = A * diag a * A⁻¹) :
    ∀ x ∈ P, x * (b : G) = (b : G) * x → x ∈ centerOf L := by
  intro x hx hxb
  have hxL : x ∈ L := hP.1 hx
  have hx1 : α ⟨x, hxL⟩ = 1 := hC ⟨x, hxL⟩ hx (Subtype.ext hxb)
  have hxQ : x ∈ blockQ L := by
    rw [← AppC.mem_pCore_iff_mem_blockQ (L := L) ⟨x, hxL⟩, ← hαk]
    exact hx1
  have hxU : x ∈ blockU L := blockQ_le_blockU hn hLL hK α hαs hαk hxQ
  have hxZ : x ∈ blockZ L := mem_blockZ_of_commute α β hβk hβe ha hαb hxU hxb.symm
  exact ⟨hxL, hxZ.2⟩

end CFSG.Quasithin.E9.Blk

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem nrmE9_BlockL2_big {X S L : Subgroup G} (hStd : Std1521 X S L) (hth : ⁅L, thompsonJ S⁆ = L)
    (_hchar : CharTwo L) (hblk : IsBlock2 X L) (hty : ∃ n : ℕ, 3 ≤ n ∧ IsLin2Type L n) :
    NrmE9 S L := by
  obtain ⟨n, hn, hLn⟩ := hty
  have hshort : IsShort2 L := hblk.1
  have hS2 : IsPGroup 2 ↥S := hStd.sylow.isPGroup
  have hLL : ⁅L, L⁆ = L := commutator_eq_self_of_isShort2_lin2_1521 (by omega) hshort hLn
  have hBJ := borel_le_normalizer_thompsonJ_l2 (by omega) hLn hshort hS2 hStd.sylowL hth
  obtain ⟨F, hF, hfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hLn
  have : Finite F := Finite.of_fintype F
  have hK : Nat.card F = 2 ^ n := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨z, hzN, hzodd, hR, hC, A, a, ha, hαz⟩ :=
    Blk.exists_torus hn hK α hαs hαk hStd.sylowL
  have hzB : (z : G) ∈ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := ⟨z.2, hzN⟩
  have hH : Subgroup.zpowers (z : G) ≤ L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hzB
  refine ⟨Subgroup.zpowers (z : G), hH.trans le_conjJoin, hH.trans hBJ, ?_, ?_⟩
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe]
    exact hzodd
  · intro H₀ _ hidx
    have hcomm : ∀ x ∈ Subgroup.zpowers (z : G), ∀ y ∈ Subgroup.zpowers (z : G),
        x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_zpow_self (z : G) i j).eq
    have hz3 : (z : G) ^ 3 ∈ H₀ :=
      pow_three_mem_of_relIndex_dvd_three hcomm hidx _ (Subgroup.mem_zpowers _)
    have hb : ((z ^ 3 : ↥L) : G) = (z : G) ^ 3 := by rw [Subgroup.coe_pow]
    refine ⟨fun v hvS hvN hvP hvH l hl => ?_, fun x hx hxH => ?_⟩
    · exact Blk.block_centralizes_of_torus hn hshort hLL hK α hαs hαk β hβk hβe hStd.sylowL hR
        ha hαz hvN (hS2.to_le (Subgroup.zpowers_le.mpr hvS)) hvP
        (by rw [hb]; exact hvH _ hz3) l hl
    · exact Blk.block_centerOf_of_torus hn hLL hK α hαs hαk β hβk hβe hStd.sylowL hC ha hαz x
        hx.1 (by rw [hb]; exact hxH _ hz3)

end CFSG.Quasithin.E9
