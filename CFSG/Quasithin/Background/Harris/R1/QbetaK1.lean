module

public import CFSG.Quasithin.Background.Harris.R1.QbetaA
public import CFSG.Quasithin.Background.Harris.R1.QbetaPerf
public import CFSG.Quasithin.Recognition.SzR1Center

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem Z_comm {a b : G} (ha : a ∈ Z) (hb : b ∈ Z) : a * b = b * a := by
  rcases h.hZcases a ha with h1 | h1 <;> rcases h.hZcases b hb with h2 | h2 <;> subst h1 <;>
    subst h2 <;> simp

theorem K1_comm_D_mem_Z {K1 : Subgroup G} (hK1 : ⁅K1, K1⁆ = K1)
    (hK1D : K1 ≤ Subgroup.normalizer (D : Set G))
    (hK1Z : ∀ k ∈ K1, ∀ s ∈ Z, k * s = s * k) {a1 a2 : G}
    (ha1 : a1 ∈ conjSub g W ⊓ Q) (ha2 : a2 ∈ conjSub g W ⊓ Q)
    (hgen : conjSub g W ⊓ Q ≤ Subgroup.closure (((Z ⊔ conjSub g Z : Subgroup G) : Set G) ∪ {a1, a2}))
    (hZcard : Nat.card Z = 2) {k : G} (hk : k ∈ K1) {x : G} (hx : x ∈ D) :
    k * x * k⁻¹ * x⁻¹ ∈ Z := by
  classical
  have hDS' : D ≤ S := fun x hx => h.hMS (h.hD hx)
  have hZc : ∀ s ∈ Z, ∀ t ∈ S, s * t = t * s := fun s hs t ht =>
    Subgroup.mem_centralizer_iff.mp (h.hSZ ht) s hs
  have hA'S : conjSub g W ⊓ Q ≤ S := fun a ha => h.vh.qs ha.2
  have hcomm_inv : ∀ c ∈ Z, ∀ y ∈ S, ∀ a ∈ S,
      (c * y) * a * (c * y)⁻¹ * a⁻¹ = y * a * y⁻¹ * a⁻¹ := by
    intro c hc y hy a ha
    have h1 : c * (y * a * y⁻¹) = (y * a * y⁻¹) * c :=
      hZc c hc _ (S.mul_mem (S.mul_mem hy ha) (S.inv_mem hy))
    calc (c * y) * a * (c * y)⁻¹ * a⁻¹ = c * (y * a * y⁻¹) * c⁻¹ * a⁻¹ := by group
      _ = (y * a * y⁻¹) * c * c⁻¹ * a⁻¹ := by rw [h1]
      _ = y * a * y⁻¹ * a⁻¹ := by group
  have hKc : ∀ k ∈ K1, ∀ c ∈ Z, k * c * k⁻¹ = c := fun k hk c hc => by
    rw [hK1Z k hk c hc]; group
  let Stab : Subgroup G :=
    { carrier := {k | k ∈ K1 ∧ k * x * k⁻¹ * x⁻¹ ∈ Z}
      one_mem' := ⟨K1.one_mem, by simpa using Z.one_mem⟩
      mul_mem' := by
        rintro k1 k2 ⟨hk1, hc1⟩ ⟨hk2, hc2⟩
        refine ⟨K1.mul_mem hk1 hk2, ?_⟩
        have e : k1 * k2 * x * (k1 * k2)⁻¹ * x⁻¹ =
            (k1 * (k2 * x * k2⁻¹ * x⁻¹) * k1⁻¹) * (k1 * x * k1⁻¹ * x⁻¹) := by group
        rw [e, hKc k1 hk1 _ hc2]
        exact Z.mul_mem hc2 hc1
      inv_mem' := by
        rintro k ⟨hk, hc⟩
        refine ⟨K1.inv_mem hk, ?_⟩
        have e : k⁻¹ * x * k⁻¹⁻¹ * x⁻¹ = k⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * k := by group
        rw [e]
        have := hKc k⁻¹ (K1.inv_mem hk) _ (Z.inv_mem hc)
        rw [show k⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * k = k⁻¹ * (k * x * k⁻¹ * x⁻¹)⁻¹ * k⁻¹⁻¹ by group]
        rw [this]
        exact Z.inv_mem hc }
  have hStabK : Stab ≤ K1 := fun k hk => hk.1
  have hconjD : ∀ k ∈ K1, k * x * k⁻¹ ∈ D := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp (hK1D hk) x).mp hx
  have hZ2 : Nat.card (↥Z × ↥Z) = 4 := by
    rw [Nat.card_prod, hZcard]
  have hidx : Nat.card (↥K1 ⧸ Stab.subgroupOf K1) ≤ 4 := by
    let f : ↥K1 → ↥Z × ↥Z := fun k =>
      (⟨(k * x * k⁻¹) * a1 * (k * x * k⁻¹)⁻¹ * a1⁻¹, h.comm_D_A' (hconjD k k.2) ha1⟩,
       ⟨(k * x * k⁻¹) * a2 * (k * x * k⁻¹)⁻¹ * a2⁻¹, h.comm_D_A' (hconjD k k.2) ha2⟩)
    have hyS : ∀ k : ↥K1, (k : G) * x * (k : G)⁻¹ ∈ S := fun k => hDS' (hconjD k k.2)
    have ha1S : a1 ∈ S := hA'S ha1
    have ha2S : a2 ∈ S := hA'S ha2
    have hwd : ∀ k k' : ↥K1, (QuotientGroup.leftRel (Stab.subgroupOf K1)).r k k' → f k = f k' := by
      intro k k' hkk'
      have hmem : (k⁻¹ * k' : ↥K1) ∈ Stab.subgroupOf K1 := QuotientGroup.leftRel_apply.mp hkk'
      obtain ⟨-, hc⟩ := Subgroup.mem_subgroupOf.mp hmem
      have hc' : ((k : G)⁻¹ * k') * x * ((k : G)⁻¹ * k')⁻¹ * x⁻¹ ∈ Z := hc
      set c := ((k : G)⁻¹ * k') * x * ((k : G)⁻¹ * k')⁻¹ * x⁻¹ with hcdef
      have e : (k' : G) * x * (k' : G)⁻¹ = c * ((k : G) * x * (k : G)⁻¹) := by
        have e0 : (k' : G) * x * (k' : G)⁻¹ = (k : G) * (c * x) * (k : G)⁻¹ := by
          rw [hcdef]; group
        rw [e0]
        have := hKc k k.2 c hc'
        calc (k : G) * (c * x) * (k : G)⁻¹ = ((k : G) * c * (k : G)⁻¹) * ((k : G) * x * (k : G)⁻¹) := by
              group
          _ = c * ((k : G) * x * (k : G)⁻¹) := by rw [this]
      have h1 := hcomm_inv c hc' _ (hyS k) a1 ha1S
      have h2 := hcomm_inv c hc' _ (hyS k) a2 ha2S
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show ((k : G) * x * (k : G)⁻¹) * a1 * ((k : G) * x * (k : G)⁻¹)⁻¹ * a1⁻¹ =
          ((k' : G) * x * (k' : G)⁻¹) * a1 * ((k' : G) * x * (k' : G)⁻¹)⁻¹ * a1⁻¹
        rw [e]; exact h1.symm
      · show ((k : G) * x * (k : G)⁻¹) * a2 * ((k : G) * x * (k : G)⁻¹)⁻¹ * a2⁻¹ =
          ((k' : G) * x * (k' : G)⁻¹) * a2 * ((k' : G) * x * (k' : G)⁻¹)⁻¹ * a2⁻¹
        rw [e]; exact h2.symm
    have hinj : Function.Injective (Quotient.lift (s := QuotientGroup.leftRel (Stab.subgroupOf K1))
        f hwd) := by
      intro q q'
      induction q using Quotient.inductionOn with | _ k => ?_
      induction q' using Quotient.inductionOn with | _ k' => ?_
      intro hf
      apply Quotient.sound
      show (QuotientGroup.leftRel (Stab.subgroupOf K1)).r k k'
      rw [QuotientGroup.leftRel_apply]
      have hf' : f k = f k' := hf
      have hE1 : ((k : G) * x * (k : G)⁻¹) * a1 * ((k : G) * x * (k : G)⁻¹)⁻¹ * a1⁻¹ =
          ((k' : G) * x * (k' : G)⁻¹) * a1 * ((k' : G) * x * (k' : G)⁻¹)⁻¹ * a1⁻¹ :=
        congrArg Subtype.val (congrArg Prod.fst hf')
      have hE2 : ((k : G) * x * (k : G)⁻¹) * a2 * ((k : G) * x * (k : G)⁻¹)⁻¹ * a2⁻¹ =
          ((k' : G) * x * (k' : G)⁻¹) * a2 * ((k' : G) * x * (k' : G)⁻¹)⁻¹ * a2⁻¹ :=
        congrArg Subtype.val (congrArg Prod.snd hf')
      set y := (k : G) * x * (k : G)⁻¹ with hy
      set y' := (k' : G) * x * (k' : G)⁻¹ with hy'
      have hyD : y ∈ D := hconjD k k.2
      have hy'D : y' ∈ D := hconjD k' k'.2
      set u := y⁻¹ * y' with hu
      have huD : u ∈ D := D.mul_mem (D.inv_mem hyD) hy'D
      have hua : ∀ a : G, y * a * y⁻¹ * a⁻¹ = y' * a * y'⁻¹ * a⁻¹ → u * a = a * u := by
        intro a hE
        have h1 : y * a * y⁻¹ = y' * a * y'⁻¹ := mul_right_cancel hE
        rw [hu]
        calc y⁻¹ * y' * a = y⁻¹ * (y' * a * y'⁻¹) * y' := by group
          _ = y⁻¹ * (y * a * y⁻¹) * y' := by rw [h1]
          _ = a * (y⁻¹ * y') := by group
      have hu1 := hua a1 hE1
      have hu2 := hua a2 hE2
      have huV : ∀ v ∈ Z ⊔ conjSub g Z, u * v = v * u := fun v hv =>
        h.hDc u huD v (h.V_le_W hv)
      have huA : ∀ a ∈ conjSub g W ⊓ Q, u * a = a * u := by
        intro a ha
        have hcl := hgen ha
        have hle : Subgroup.closure (((Z ⊔ conjSub g Z : Subgroup G) : Set G) ∪ {a1, a2}) ≤
            Subgroup.centralizer ({u} : Set G) := by
          rw [Subgroup.closure_le]
          intro t ht
          rcases ht with ht | ht
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (huV t ht).symm
          · rcases ht with rfl | ht
            · exact Subgroup.mem_centralizer_singleton_iff.mpr hu1.symm
            · rw [Set.mem_singleton_iff] at ht
              subst ht
              exact Subgroup.mem_centralizer_singleton_iff.mpr hu2.symm
        have := hle hcl
        exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
      have huZ : u ∈ Z := h.mem_Z_of_comm huD huA
      have hkk : ((k⁻¹ * k' : ↥K1) : G) ∈ Stab := by
        refine ⟨(k⁻¹ * k' : ↥K1).2, ?_⟩
        have hy'u : y' = y * u := by rw [hu]; group
        have hxu : (k : G)⁻¹ * y' * k = x * u := by
          rw [hy'u]
          calc (k : G)⁻¹ * (y * u) * k = ((k : G)⁻¹ * y * k) * ((k : G)⁻¹ * u * k) := by group
            _ = x * u := by
              have e1 : (k : G)⁻¹ * y * k = x := by rw [hy]; group
              have e2 : (k : G)⁻¹ * u * k = u := by
                have := hKc (k : G)⁻¹ (K1.inv_mem k.2) u huZ
                simpa using this
              rw [e1, e2]
        have e3 : ((k : G)⁻¹ * k') * x * ((k : G)⁻¹ * k')⁻¹ * x⁻¹ = (x * u) * x⁻¹ := by
          rw [← hxu, hy']; group
        show ((k : G)⁻¹ * k') * x * ((k : G)⁻¹ * k')⁻¹ * x⁻¹ ∈ Z
        rw [e3]
        have hxS : x ∈ S := hDS' hx
        have h1 : u * x = x * u := hZc u huZ x hxS
        have e4 : (x * u) * x⁻¹ = u := by
          calc (x * u) * x⁻¹ = (u * x) * x⁻¹ := by rw [h1]
            _ = u := by group
        rw [e4]
        exact huZ
      exact hkk
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [hZ2] at hcard
    exact hcard
  have hK1S : K1 ≤ Stab := perfect_le_of_index_le_four hK1 hStabK hidx
  exact (hK1S hk).2

theorem K1_comm_D {K1 : Subgroup G} (hK1 : ⁅K1, K1⁆ = K1)
    (hK1D : K1 ≤ Subgroup.normalizer (D : Set G))
    (hK1Z : ∀ k ∈ K1, ∀ s ∈ Z, k * s = s * k) {a1 a2 : G}
    (ha1 : a1 ∈ conjSub g W ⊓ Q) (ha2 : a2 ∈ conjSub g W ⊓ Q)
    (hgen : conjSub g W ⊓ Q ≤ Subgroup.closure (((Z ⊔ conjSub g Z : Subgroup G) : Set G) ∪ {a1, a2}))
    (hZcard : Nat.card Z = 2) {k : G} (hk : k ∈ K1) {x : G} (hx : x ∈ D) :
    k * x = x * k := by
  refine SzR1.centralizes_of_perfect (K := K1) (Zs := Z) (y := x) hK1 hK1Z
    (fun s hs t ht => h.Z_comm hs ht) (fun k' hk' => ?_) k hk
  refine ⟨k' * x * k'⁻¹ * x⁻¹, h.K1_comm_D_mem_Z hK1 hK1D hK1Z ha1 ha2 hgen hZcard hk' hx, ?_⟩
  group

end QD

end CFSG.Quasithin.Background.Harris.R1
