module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312Ext
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312Gen0

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312
open scoped Pointwise

theorem odd_sup_of_normal {H : Type} [Group H] [Finite H] (N N₀ : Subgroup H) [N.Normal]
    [N₀.Normal] (hN : Odd (Nat.card N)) (hN₀ : Odd (Nat.card N₀)) :
    Odd (Nat.card ↥(N ⊔ N₀)) := by
  set M := N ⊔ N₀ with hM
  have hle : N₀ ≤ M := le_sup_right
  have hmul := Subgroup.card_mul_index (N₀.subgroupOf M)
  have hcardN₀ : Nat.card ↥(N₀.subgroupOf M) = Nat.card ↥N₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  let f : ↥N →* ↥M ⧸ N₀.subgroupOf M :=
    (QuotientGroup.mk' (N₀.subgroupOf M)).comp
      { toFun := fun n => ⟨n.1, Subgroup.mem_sup_left n.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : H) ∈ ((N : Set H) * (N₀ : Set H)) := by
        rw [← Subgroup.mul_normal N N₀]
        exact x.2
      obtain ⟨n, hn, b, hb, hnb⟩ := Set.mem_mul.mp hx
      refine ⟨⟨n, hn⟩, ?_⟩
      show (QuotientGroup.mk (⟨n, Subgroup.mem_sup_left hn⟩ : ↥M) : ↥M ⧸ N₀.subgroupOf M) =
        QuotientGroup.mk x
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (⟨n, Subgroup.mem_sup_left hn⟩ : ↥M)⁻¹ * x = ⟨b, Subgroup.mem_sup_right hb⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk]
        rw [← hnb]
        group
      rw [this]
      exact hb
  have hidx : (N₀.subgroupOf M).index ∣ Nat.card N :=
    dvd_trans (card_dvd_of_surj f hf) (dvd_refl _)
  have hodd_idx : Odd (N₀.subgroupOf M).index := by
    exact Odd.of_dvd_nat hN hidx
  rw [← hmul, hcardN₀]
  exact Odd.mul hN₀ hodd_idx

theorem oddCore_odd (H : Type) [Group H] [Finite H] : Odd (Nat.card (CFSG.oddCore H)) := by
  set S : Set (Subgroup H) := {N | N.Normal ∧ Odd (Nat.card N)} with hS
  have hbot : (⊥ : Subgroup H) ∈ S := ⟨inferInstance, by rw [Subgroup.card_bot]; exact odd_one⟩
  have hbdd : BddAbove ((fun N : Subgroup H => Nat.card N) '' S) := by
    refine ⟨Nat.card H, ?_⟩
    rintro _ ⟨N, -, rfl⟩
    exact Subgroup.card_le_card_group N
  obtain ⟨N₀, hN₀S, hN₀max⟩ : ∃ N₀ ∈ S, ∀ N ∈ S, Nat.card N ≤ Nat.card N₀ := by
    have hmem := Nat.sSup_mem (⟨_, ⟨⊥, hbot, rfl⟩⟩ : ((fun N : Subgroup H => Nat.card N) '' S).Nonempty)
      hbdd
    obtain ⟨N₀, hN₀S, hN₀c⟩ := hmem
    refine ⟨N₀, hN₀S, fun N hN => ?_⟩
    dsimp only at hN₀c
    rw [hN₀c]
    exact le_csSup hbdd ⟨N, hN, rfl⟩
  have hN₀n : N₀.Normal := hN₀S.1
  have hN₀o : Odd (Nat.card N₀) := hN₀S.2
  have hall : ∀ N ∈ S, N ≤ N₀ := by
    intro N hN
    have hN' : N.Normal := hN.1
    have hNo : Odd (Nat.card N) := hN.2
    have hMS : N ⊔ N₀ ∈ S := ⟨inferInstance, odd_sup_of_normal N N₀ hNo hN₀o⟩
    have hle : Nat.card ↥(N ⊔ N₀) ≤ Nat.card ↥N₀ := hN₀max _ hMS
    have heq : N₀ = N ⊔ N₀ := Subgroup.eq_of_le_of_card_ge le_sup_right hle
    rw [heq]
    exact le_sup_left
  have hsSup : sSup S = N₀ := le_antisymm (sSup_le hall) (le_sSup hN₀S)
  show Odd (Nat.card ↥(sSup S))
  rw [hsSup]
  exact hN₀o

theorem card_eq_quot_mul_oddCore (H : Type) [Group H] [Finite H] :
    Nat.card H = Nat.card (H ⧸ CFSG.oddCore H) * Nat.card (CFSG.oddCore H) := by
  rw [mul_comm, ← Subgroup.card_mul_index (CFSG.oddCore H)]
  rfl

theorem inter_oddCore_eq_one {Q : Type} [Group Q] [Finite Q] {B J : Subgroup Q} (hBJ : B ≤ J)
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)))
    (b : ↥B) (hb : (Subgroup.inclusion hBJ b : ↥J) ∈ CFSG.oddCore ↥J) : b = 1 := by
  let K : Subgroup ↥B := (CFSG.oddCore ↥J).comap (Subgroup.inclusion hBJ)
  have hKodd : Odd (Nat.card K) := by
    let f : ↥K →* ↥(CFSG.oddCore ↥J) :=
      { toFun := fun k => ⟨Subgroup.inclusion hBJ k.1, k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      intro x y hxy
      have h1 : (Subgroup.inclusion hBJ x.1 : ↥J) = Subgroup.inclusion hBJ y.1 :=
        congrArg Subtype.val hxy
      exact Subtype.ext (Subgroup.inclusion_injective hBJ h1)
    exact Odd.of_dvd_nat (oddCore_odd ↥J) (card_dvd_of_injective f hinj)
  have hK : K = ⊥ := odd_normal_eq_bot hS heven K hKodd
  have hbK : b ∈ K := hb
  rw [hK, Subgroup.mem_bot] at hbK
  exact hbK

theorem card_quot_oddCore_eq_of_sup {Q : Type} [Group Q] [Finite Q] {B J : Subgroup Q}
    (hBJ : B ≤ J) (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B))
    (heven : Even (Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)))
    (hJ : J ≤ B ⊔ (CFSG.oddCore ↥J).map J.subtype) :
    Nat.card (↥J ⧸ CFSG.oddCore ↥J) = Nat.card ↥B := by
  let OL : Subgroup Q := (CFSG.oddCore ↥J).map J.subtype
  have hBN : B ≤ Subgroup.normalizer (OL : Set Q) := le_normalizer_oddCore hBJ
  let f : ↥B →* ↥J ⧸ CFSG.oddCore ↥J :=
    (QuotientGroup.mk' (CFSG.oddCore ↥J)).comp (Subgroup.inclusion hBJ)
  have hcov : ∀ x : ↥J, ∃ b : ↥B, ∃ o ∈ CFSG.oddCore ↥J, x = Subgroup.inclusion hBJ b * o :=
    cover_of_sup hBJ OL hBN hJ (CFSG.oddCore ↥J) (fun o ho hoJ => by
      rw [Subgroup.mem_map] at ho
      obtain ⟨x, hx, rfl⟩ := ho
      exact ⟨x, hx, rfl⟩)
  have hsurj : Function.Surjective f := surj_of_cover hBJ (CFSG.oddCore ↥J) hcov
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro b hb
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    exact inter_oddCore_eq_one hBJ hS heven b hb
  exact Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hsurj⟩).toEquiv.symm

end CFSG.Quasithin.H13.NF314ptA312
