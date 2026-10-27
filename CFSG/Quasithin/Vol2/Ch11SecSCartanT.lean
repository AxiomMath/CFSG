module

public import CFSG.Quasithin.Vol2.Ch11SecANat2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint SecA

variable {G : Type} [Group G]

theorem autOn_eq_map {V A B : Subgroup G} (hAB : A ≤ B)
    (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autOn A V = (A.subgroupOf B).map (conjHomL V B hB) := by
  rw [← range_conjHomL V A (hAB.trans hB)]
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, hAB a.2⟩, a.2, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

theorem autOn_sup {V A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autOn (A ⊔ B) V = autOn A V ⊔ autOn B V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hA hB

theorem autOn_mono {V A B : Subgroup G} (hAB : A ≤ B) : autOn A V ≤ autOn B V :=
  Subgroup.map_mono fun _ hx => hAB hx

theorem le_of_autOn_le {V X Y Z : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hXC : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) (hY : Y ≤ X) (hZ : Z ≤ X)
    (h : autOn Y V ≤ autOn Z V) : Y ≤ Z := by
  intro y hy
  obtain ⟨z, hz, hzy⟩ := h (conjV_mem_autOn hy (hX (hY hy)))
  have hz' : (z : G) ∈ Z := hz
  have hzy' : conjV V z z.2 = conjV V y (hX (hY hy)) := hzy
  have hc : (z : G)⁻¹ * y ∈ X ⊓ Subgroup.centralizer (V : Set G) := by
    refine ⟨X.mul_mem (X.inv_mem (hZ hz')) (hY hy), ?_⟩
    show _ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hzy'
    simp only [conjV_apply_coe] at this
    calc v * ((z : G)⁻¹ * y) = (z : G)⁻¹ * ((z : G) * v * (z : G)⁻¹) * y := by group
      _ = (z : G)⁻¹ * (y * v * y⁻¹) * y := by rw [this]
      _ = (z : G)⁻¹ * y * v := by group
  rw [hXC, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc ▸ hz'

theorem card_autOn_eq {V X Y : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hXC : X ⊓ Subgroup.centralizer (V : Set G) = ⊥) (hY : Y ≤ X) :
    Nat.card ↥(autOn Y V) = Nat.card ↥Y := by
  rw [autOn_eq_map hY hX]
  have hinj : Function.Injective (conjHomL V X hX) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjHomL, hXC]
    exact Subgroup.bot_subgroupOf _
  rw [Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv

theorem relIndex_autOn_dvd {V A B : Subgroup G} (hAB : A ≤ B)
    (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    (autOn A V).relIndex (autOn B V) ∣ A.relIndex B := by
  rw [autOn_eq_map hAB hB, autOn_eq_map le_rfl hB, Subgroup.subgroupOf_self,
    Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  exact (Subgroup.index_dvd_of_le le_sup_left : _ ∣ (A.subgroupOf B).index)

theorem inf_eq_bot_of_odd [Finite G] {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card ↥B)) : A ⊓ B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (hA.to_le (inf_le_left : A ⊓ B ≤ A)).exists_card_eq
  have hdvd : Nat.card ↥(A ⊓ B) ∣ Nat.card ↥B := Subgroup.card_dvd_of_le inf_le_right
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨m, hm⟩ := hdvd
    have h2 : 2 ∣ Nat.card ↥B := ⟨2 ^ (k - 1) * m, by
      rw [hm, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]⟩
    exact (Nat.not_even_iff_odd.mpr hB) (even_iff_two_dvd.mpr h2)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

end CFSG.Quasithin.Vol2.Ch11.SecS
