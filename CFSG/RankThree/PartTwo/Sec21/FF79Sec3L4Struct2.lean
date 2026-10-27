module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Struct
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructBase
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructElem
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructA5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 Subgroup

variable {H : Type} [Group H] [Finite H] {β : MulAut H} {Z K : Subgroup H} {z₀ : H}
variable (hd : FF79APData β Z K z₀)
include hd

theorem K_ne_layer : K ≠ layer H := by
  intro hKL
  obtain ⟨e0⟩ := hd.K_a5
  have e : ↥(layer H) ≃* alternatingGroup (Fin 5) := (MulEquiv.subgroupCongr hKL.symm).trans e0
  haveI := layer_normal_of_ap (H := H)
  obtain ⟨A', hA', hZA'⟩ := hd.A4
  haveI := hA'.1
  have hp : IsPGroup 3 A' := IsElementaryAbelian.isPGroup 3 ↥A'
  obtain ⟨P, -, hP2, hPbot, hPstab⟩ := exists_normalized_two_subgroup e hp
  obtain ⟨T, hTA, hT, hTZ⟩ := exists_elemAb_compl hA' hZA' hd.Z_card
  exact hd.no_rank2 P T hP2 hPbot hT hTZ
    (le_nor_of_stable fun a ha x hx => hPstab a (hTA ha) x hx)

theorem ap_absyl :
    ∃ S : Subgroup H, S ≤ layer H ∧ IsSylowOf 3 S (layer H) ∧ IsMulCommutative S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S0, hS0, hc⟩ := hd.absyl
  haveI := layer_normal_of_ap (H := H)
  obtain P : Sylow 3 ↥(layer H) := Classical.arbitrary _
  set S : Subgroup H := (P : Subgroup ↥(layer H)).map (layer H).subtype with hS
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hSp : IsPGroup 3 S :=
    IsPGroup.of_card (n := k) (by rw [hS, Subgroup.card_map_of_injective
      (layer H).subtype_injective, hk])
  have hSL : S ≤ layer H := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨S, hSL, ⟨hSL, hSp, ?_⟩, ⟨⟨fun a b => ?_⟩⟩⟩
  · have h1 := Subgroup.relIndex_mul_index hSL
    rw [hS, Subgroup.index_map_subtype] at h1
    have hpos : 0 < (layer H).index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    have h2 : S.relIndex (layer H) = (P : Subgroup ↥(layer H)).index :=
      Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h2]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 P.not_dvd_index
  · apply Subtype.ext
    exact pgroup_comm_of_absyl hS0 hc hSp a a.2 b b.2

theorem ap_inv3 : ∀ t u v : H, t ∈ layer H → orderOf t = 2 → u ∈ layer H → v ∈ layer H →
    orderOf u = 3 → orderOf v = 3 → u * t = t * u → v * t = t * v → u * v = v * u →
    v ∈ Subgroup.zpowers u := by
  intro t u v ht ht2 hu hv hu3 hv3 hut hvt huv
  by_contra hvu
  have hv3' : v ^ 3 = 1 := by rw [← hv3]; exact pow_orderOf_eq_one v
  have hu3' : u ^ 3 = 1 := by rw [← hu3]; exact pow_orderOf_eq_one u
  have hc : ∀ a ∈ ({u, v} : Set H), ∀ b ∈ ({u, v} : Set H), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact huv
    · exact huv.symm
    · rfl
  have h3 : ∀ a ∈ ({u, v} : Set H), a ^ 3 = 1 := by
    rintro a (rfl | rfl)
    · exact hu3'
    · exact hv3'
  have hcl : closure ({u, v} : Set H) ≤ layer H := by
    rw [closure_le]
    rintro a (rfl | rfl)
    · exact hu
    · exact hv
  have hcen : closure ({u, v} : Set H) ≤ Subgroup.centralizer ({t} : Set H) := by
    rw [closure_le]
    rintro a (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.2 hut
    · exact Subgroup.mem_centralizer_singleton_iff.2 hvt
  obtain ⟨T, hTle, hT⟩ := exists_isElemAb_of_card_le (k := 2) hc h3
    (by simpa using nine_le_card_closure_pair huv hu3 hv3' hvu)
  have hTZ : T ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxT, hxZ⟩
    exact (Subgroup.mem_bot).2 (Z_inf_L hd hxZ (hcl (hTle hxT)))
  have hP2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2]; norm_num)
  have hPbot : zpowers t ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at ht2
    omega
  refine hd.no_rank2 (zpowers t) T hP2 hPbot hT hTZ (le_nor_of_stable ?_)
  rintro a ha _ ⟨n, rfl⟩
  have hac : Commute a t := Subgroup.mem_centralizer_singleton_iff.1 (hcen (hTle ha))
  exact ⟨n, ((hac.zpow_right n).mul_inv_cancel).symm⟩

theorem ap_outer : ∀ e : H, e ∈ layer H → ¬ ∀ l ∈ layer H, β l = e * l * e⁻¹ := by
  intro e he hall
  haveI := L_facts_simple hd
  have hLmul : ∀ x y : H, x ∈ layer H → y ∈ layer H → x * y * x⁻¹ ∈ layer H :=
    fun x y hx hy => (layer H).mul_mem ((layer H).mul_mem hx hy) ((layer H).inv_mem hx)
  have hβe : β e = e := by simpa using hall e he
  have hKe : ∀ k ∈ K, k * e = e * k := by
    intro k hk
    have h := hall k (K_le_L hd hk)
    rw [hd.K_fix k hk] at h
    calc k * e = (e * k * e⁻¹) * e := by rw [← h]
      _ = e * k := by group
  have hpow : ∀ n : ℕ, ∀ l ∈ layer H, (β ^ n) l = e ^ n * l * (e ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro l _; simp
    | succ n ih =>
      intro l hl
      have hmem : e ^ n * l * (e ^ n)⁻¹ ∈ layer H :=
        (layer H).mul_mem ((layer H).mul_mem (pow_mem he n) hl) ((layer H).inv_mem (pow_mem he n))
      rw [pow_succ', MulAut.mul_apply, ih l hl, hall _ hmem, pow_succ']
      group
  have he3 : e ^ 3 = 1 := by
    refine L_central hd (pow_mem he 3) fun w hw => ?_
    have h := hpow 3 w hw
    rw [hd.beta3, MulAut.one_apply] at h
    calc w * e ^ 3 = (e ^ 3 * w * (e ^ 3)⁻¹) * e ^ 3 := by rw [← h]
      _ = e ^ 3 * w := by group
  by_cases he1 : e = 1
  · subst he1
    have hfix : ∀ l ∈ layer H, β l = l := fun l hl => by simpa using hall l hl
    haveI hnor : (K.subgroupOf (layer H)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hd.K_nor g (hfix g g.2) n hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf (layer H)) with h | h
    · obtain ⟨a, haK, ha3⟩ := K_order3 hd
      have hmem : (⟨a, K_le_L hd haK⟩ : ↥(layer H)) ∈ K.subgroupOf (layer H) :=
        Subgroup.mem_subgroupOf.2 haK
      rw [h, Subgroup.mem_bot] at hmem
      have : a = 1 := congrArg Subtype.val hmem
      rw [this, orderOf_one] at ha3
      omega
    · exact K_ne_layer hd (le_antisymm (K_le_L hd) (Subgroup.subgroupOf_eq_top.1 h))
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have horder : orderOf e = 3 := orderOf_eq_prime he3 he1
    obtain ⟨a, haK, ha3⟩ := K_order3 hd
    refine no_fixed_pair hd (x := a) (y := e) (K_le_L hd haK) he ha3 horder (hKe a haK)
      (hd.K_fix a haK) hβe ?_
    intro hmem
    exact he1 (K_central hd ((zpowers_le.2 haK) hmem) fun w hw => hKe w hw)

end CFSG.RankThree.PartTwo.Sec21.FF79
