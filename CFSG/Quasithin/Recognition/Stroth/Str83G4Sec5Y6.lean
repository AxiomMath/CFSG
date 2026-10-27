module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5Y
public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape
public import CFSG.Quasithin.Recognition.Stroth.Str86ChiefFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.RankLemma

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem relIndex_sup_left_of_le_normalizer {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hH
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hH).toEquiv.symm

private theorem card_dvd_relIndex_sub_one_of_fixed_mem {D Y M : Subgroup G} (hYM : Y ≤ M)
    (hDM : D ≤ Subgroup.normalizer (M : Set G)) (hDY : D ≤ Subgroup.normalizer (Y : Set G))
    (hfix : ∀ k ∈ D, k ≠ 1 → ∀ m ∈ M, k * m * k⁻¹ = m → m ∈ Y)
    (hcop : Nat.Coprime (Nat.card D) (Nat.card Y)) : Nat.card D ∣ Y.relIndex M - 1 := by
  classical
  let _ : MulAction D M :=
    MulAction.compHom M (M.normalizerMonoidHom.comp (Subgroup.inclusion hDM))
  have hsmul : ∀ (k : D) (m : M), ((k • m : M) : G) = (k : G) * m * (k : G)⁻¹ :=
    fun k m => rfl
  let P : SubMulAction D M :=
    { carrier := {m | (m : G) ∉ Y}
      smul_mem' := fun k m hm h => hm <| by
        rw [hsmul] at h
        exact (Subgroup.mem_normalizer_iff.mp (hDY k.2) m).mpr h }
  let := Fintype.ofFinite D
  let := Fintype.ofFinite P
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group D P
  have h1 : Fintype.card (MulAction.fixedBy P (1 : D)) = Fintype.card P :=
    Fintype.card_congr (Equiv.subtypeUnivEquiv fun y => one_smul D y)
  have h2 : ∀ k ∈ Finset.univ.erase (1 : D), Fintype.card (MulAction.fixedBy P k) = 0 := by
    intro k hk
    have hk1 : k ≠ 1 := Finset.ne_of_mem_erase hk
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun p => ?_⟩
    have hp : k • (p : P) = p := p.2
    have h3 : (k : G) * ((p : P) : M) * (k : G)⁻¹ = ((p : P) : M) := by
      rw [← hsmul, ← SubMulAction.val_smul, hp]
    exact (p : P).2 (hfix k k.2 (fun h => hk1 (Subtype.ext h)) _ ((p : P) : M).2 h3)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1), h1, Finset.sum_congr rfl h2,
    Finset.sum_const_zero, add_zero] at hB
  have hdvdP : Nat.card D ∣ Nat.card P := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hB]
    exact Dvd.intro_left _ rfl
  have hsplit : Nat.card M = Nat.card Y + Nat.card P := by
    have e1 : {m : M // (m : G) ∈ Y} ≃ Y :=
      { toFun := fun m => ⟨m.1, m.2⟩
        invFun := fun y => ⟨⟨y, hYM y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have e2 : {m : M // ¬ (m : G) ∈ Y} ≃ P := Equiv.subtypeEquivRight fun _ => Iff.rfl
    rw [← Nat.card_congr (Equiv.sumCompl fun m : M => (m : G) ∈ Y), Nat.card_sum,
      Nat.card_congr e1, Nat.card_congr e2]
  have hrel : Y.relIndex M * Nat.card Y = Nat.card M := by
    have := Subgroup.relIndex_mul_card (H := Y) (K := M)
    rwa [inf_eq_left.mpr hYM] at this
  have hMpos : 0 < Nat.card M := Nat.card_pos
  obtain ⟨s, hs⟩ : ∃ s, Y.relIndex M = s + 1 :=
    ⟨Y.relIndex M - 1, by
      rcases Nat.eq_zero_or_pos (Y.relIndex M) with h | h
      · rw [h, zero_mul] at hrel
        omega
      · omega⟩
  have hP : Nat.card P = Nat.card Y * s := by
    rw [hs, add_mul, one_mul] at hrel
    rw [mul_comm]
    omega
  rw [hs, Nat.add_sub_cancel]
  exact hcop.dvd_of_dvd_mul_left (hP ▸ hdvdP)

private theorem mem_centralizer_of_conj_eq_of_fpf {X Z : Subgroup G} {k u : G}
    (hX : IsElemAbelian 2 X) (hZX : Z ≤ X) (hkZ : k ∈ Subgroup.centralizer (Z : Set G))
    (hkX : k ∈ Subgroup.normalizer (X : Set G)) (hk : Odd (orderOf k))
    (hfpf : ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ Z → x ∈ Z)
    (hXu : ∀ x ∈ X, x * u * x⁻¹ * u⁻¹ ∈ Z) (huZ : u ∈ Subgroup.centralizer (Z : Set G))
    (hku : k * u * k⁻¹ = u) : u ∈ Subgroup.centralizer (X : Set G) := by
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    simpa using hX.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨y, hy⟩ : ↥X)
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx => by simpa [sq] using hX.2 x hx
  have hdY : ∀ z ∈ X, k * z * k⁻¹ ∈ X := fun z hz => (Subgroup.mem_normalizer_iff.mp hkX z).mp hz
  have hkinv : k⁻¹ * u * k = u := by
    calc k⁻¹ * u * k = k⁻¹ * (k * u * k⁻¹) * k := by rw [hku]
      _ = u := by group
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hmem : x ∈ Subgroup.centralizer ({u} : Set G) := by
    refine mem_of_comm_mem_of_fixedPointFree hX2 hXc (fun z hz => ?_) hx hdY (fun z hz => ?_) hk
      hfpf ?_
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp huZ z hz)
    · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      calc k * z * k⁻¹ * u = k * z * k⁻¹ * (k * u * k⁻¹) := by rw [hku]
        _ = k * (z * u) * k⁻¹ := by group
        _ = k * (u * z) * k⁻¹ := by rw [hz]
        _ = (k * u * k⁻¹) * (k * z * k⁻¹) := by group
        _ = u * (k * z * k⁻¹) := by rw [hku]
    · obtain ⟨c, hcdef⟩ : ∃ c, c = x * u * x⁻¹ * u⁻¹ := ⟨_, rfl⟩
      have hcZ : c ∈ Z := hcdef ▸ hXu x hx
      have hcX : c ∈ X := hZX hcZ
      have hkc : k * c * k⁻¹ = c := by
        have h := Subgroup.mem_centralizer_iff.mp hkZ c hcZ
        calc k * c * k⁻¹ = c * k * k⁻¹ := by rw [h]
          _ = c := by group
      have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left (hX2 x hx)).symm
      have hxu : x⁻¹ * u * x = c * u := by
        rw [hcdef, hxinv]
        group
      have hau : (k * x * k⁻¹) * u * (k * x * k⁻¹)⁻¹ = c * u := by
        calc (k * x * k⁻¹) * u * (k * x * k⁻¹)⁻¹ = k * x * (k⁻¹ * u * k) * x⁻¹ * k⁻¹ := by group
          _ = k * (x * u * x⁻¹ * u⁻¹ * u) * k⁻¹ := by rw [hkinv]; group
          _ = k * (c * u) * k⁻¹ := by rw [← hcdef]
          _ = (k * c * k⁻¹) * (k * u * k⁻¹) := by group
          _ = c * u := by rw [hkc, hku]
      have hac : (k * x * k⁻¹) * c * (k * x * k⁻¹)⁻¹ = c := by
        rw [hXc _ (hdY x hx) c hcX]
        group
      have hconj : (k * x * k⁻¹ * x⁻¹) * u * (k * x * k⁻¹ * x⁻¹)⁻¹ = u := by
        calc (k * x * k⁻¹ * x⁻¹) * u * (k * x * k⁻¹ * x⁻¹)⁻¹
            = (k * x * k⁻¹) * (x⁻¹ * u * x) * (k * x * k⁻¹)⁻¹ := by group
          _ = (k * x * k⁻¹) * (c * u) * (k * x * k⁻¹)⁻¹ := by rw [hxu]
          _ = ((k * x * k⁻¹) * c * (k * x * k⁻¹)⁻¹) *
                ((k * x * k⁻¹) * u * (k * x * k⁻¹)⁻¹) := by group
          _ = c * (c * u) := by rw [hac, hau]
          _ = u := by rw [← mul_assoc, hX2 c hcX, one_mul]
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc k * x * k⁻¹ * x⁻¹ * u
          = (k * x * k⁻¹ * x⁻¹) * u * (k * x * k⁻¹ * x⁻¹)⁻¹ * (k * x * k⁻¹ * x⁻¹) := by group
        _ = u * (k * x * k⁻¹ * x⁻¹) := by rw [hconj]
  exact Subgroup.mem_centralizer_singleton_iff.mp hmem

private theorem exists_hom_zmod_two_ne_one {Z : Subgroup G}
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a * a = 1) {c : G} (hc : c ∈ Z)
    (hc1 : c ≠ 1) : ∃ θ : ↥Z →* Multiplicative (ZMod 2), θ ⟨c, hc⟩ ≠ 1 := by
  classical
  let _ : CommGroup ↥Z :=
    { (inferInstance : Group ↥Z) with mul_comm := fun x y => Subtype.ext (hZc x x.2 y y.2) }
  let _ : Module (ZMod 2) (Additive ↥Z) := AddCommGroup.zmodModule fun x => by
    induction x using Additive.rec with | _ a => ?_
    show Additive.ofMul (a ^ 2) = Additive.ofMul 1
    congr 1
    exact Subtype.ext (by simpa [sq] using hZ2 a a.2)
  have hx : Additive.ofMul (⟨c, hc⟩ : ↥Z) ≠ 0 := fun h => hc1 (by
    have := congrArg (fun z : Additive ↥Z => ((Additive.toMul z : ↥Z) : G)) h
    simpa using this)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx
  refine ⟨AddMonoidHom.toMultiplicativeRight f.toAddMonoidHom, fun h => ?_⟩
  have h1 : f (Additive.ofMul ⟨c, hc⟩) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  rw [hf] at h1
  exact one_ne_zero h1

private theorem relIndex_inf_centralizer_le_of_isChiefStep {L X Z Q J : Subgroup G}
    (hX : IsElemAbelian 2 X) (hZX : Z ≤ X) (hXQ : ∀ x ∈ X, ∀ u ∈ Q, x * u * x⁻¹ * u⁻¹ ∈ Z)
    (hQZ : Q ≤ Subgroup.centralizer (Z : Set G)) (hLZ : L ≤ Subgroup.centralizer (Z : Set G))
    (hLX : L ≤ Subgroup.normalizer (X : Set G))
    (hstep : IsChiefStep L Q (Q ⊓ Subgroup.centralizer (X : Set G)) Q) :
    (Q ⊓ Subgroup.centralizer (X : Set G)).relIndex (Q ⊓ Subgroup.centralizer (J : Set G)) ≤
      J.relIndex X := by
  classical
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => by
    simpa using hX.1.is_comm.comm (⟨x, hx⟩ : ↥X) (⟨y, hy⟩ : ↥X)
  have hX2 : ∀ x ∈ X, x * x = 1 := fun x hx => by simpa [sq] using hX.2 x hx
  have hmulL : ∀ x ∈ X, ∀ x' ∈ X, ∀ u ∈ Q, (x * x') * u * (x * x')⁻¹ * u⁻¹ =
      (x * u * x⁻¹ * u⁻¹) * (x' * u * x'⁻¹ * u⁻¹) := by
    intro x hx x' hx' u hu
    have h1 : x * (x' * u * x'⁻¹ * u⁻¹) * x⁻¹ = x' * u * x'⁻¹ * u⁻¹ := by
      rw [hXc x hx _ (hZX (hXQ x' hx' u hu))]
      group
    have h2 := hXc _ (hZX (hXQ x hx u hu)) _ (hZX (hXQ x' hx' u hu))
    calc (x * x') * u * (x * x')⁻¹ * u⁻¹
        = (x * (x' * u * x'⁻¹ * u⁻¹) * x⁻¹) * (x * u * x⁻¹ * u⁻¹) := by group
      _ = (x' * u * x'⁻¹ * u⁻¹) * (x * u * x⁻¹ * u⁻¹) := by rw [h1]
      _ = (x * u * x⁻¹ * u⁻¹) * (x' * u * x'⁻¹ * u⁻¹) := h2.symm
  have hmulR : ∀ x ∈ X, ∀ u ∈ Q, ∀ u' ∈ Q, x * (u * u') * x⁻¹ * (u * u')⁻¹ =
      (x * u * x⁻¹ * u⁻¹) * (x * u' * x⁻¹ * u'⁻¹) := by
    intro x hx u hu u' hu'
    have h1 : (x * u' * x⁻¹ * u'⁻¹) * u = u * (x * u' * x⁻¹ * u'⁻¹) :=
      Subgroup.mem_centralizer_iff.mp (hQZ hu) _ (hXQ x hx u' hu')
    calc x * (u * u') * x⁻¹ * (u * u')⁻¹
        = (x * u * x⁻¹ * u⁻¹) * (u * (x * u' * x⁻¹ * u'⁻¹) * u⁻¹) := by group
      _ = (x * u * x⁻¹ * u⁻¹) * ((x * u' * x⁻¹ * u'⁻¹) * u * u⁻¹) := by rw [← h1]
      _ = (x * u * x⁻¹ * u⁻¹) * (x * u' * x⁻¹ * u'⁻¹) := by group
  have hinvR : ∀ x ∈ X, ∀ u ∈ Q, x * u⁻¹ * x⁻¹ * u⁻¹⁻¹ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by
    intro x hx u hu
    have h1 : (x * u * x⁻¹ * u⁻¹)⁻¹ * u = u * (x * u * x⁻¹ * u⁻¹)⁻¹ :=
      Subgroup.mem_centralizer_iff.mp (hQZ hu) _ (Z.inv_mem (hXQ x hx u hu))
    calc x * u⁻¹ * x⁻¹ * u⁻¹⁻¹ = u⁻¹ * ((x * u * x⁻¹ * u⁻¹)⁻¹ * u) := by group
      _ = u⁻¹ * (u * (x * u * x⁻¹ * u⁻¹)⁻¹) := by rw [h1]
      _ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
  obtain ⟨u₀, hu₀Q, hu₀Y⟩ := SetLike.exists_of_lt hstep.2.2.1
  obtain ⟨x₀, hx₀, hx₀u₀⟩ : ∃ x₀ ∈ X, x₀ * u₀ ≠ u₀ * x₀ := by
    by_contra h
    push Not at h
    exact hu₀Y (Subgroup.mem_inf.mpr ⟨hu₀Q, Subgroup.mem_centralizer_iff.mpr h⟩)
  have hc₀Z : x₀ * u₀ * x₀⁻¹ * u₀⁻¹ ∈ Z := hXQ x₀ hx₀ u₀ hu₀Q
  have hc₀1 : x₀ * u₀ * x₀⁻¹ * u₀⁻¹ ≠ 1 := fun h => hx₀u₀ (by
    calc x₀ * u₀ = x₀ * u₀ * x₀⁻¹ * u₀⁻¹ * (u₀ * x₀) := by group
      _ = u₀ * x₀ := by rw [h, one_mul])
  obtain ⟨θ, hθ⟩ := exists_hom_zmod_two_ne_one (fun a ha b hb => hXc a (hZX ha) b (hZX hb))
    (fun a ha => hX2 a (hZX ha)) hc₀Z hc₀1
  obtain ⟨θ', hθ'⟩ : ∃ θ' : G → Multiplicative (ZMod 2), ∀ g (h : g ∈ Z), θ' g = θ ⟨g, h⟩ :=
    ⟨fun g => if h : g ∈ Z then θ ⟨g, h⟩ else 1, fun g h => dif_pos h⟩
  have hθ'mul : ∀ a ∈ Z, ∀ b ∈ Z, θ' (a * b) = θ' a * θ' b := fun a ha b hb => by
    rw [hθ' _ (Z.mul_mem ha hb), hθ' _ ha, hθ' _ hb]
    exact map_mul θ ⟨a, ha⟩ ⟨b, hb⟩
  have hθ'one : θ' 1 = 1 := by
    rw [hθ' _ Z.one_mem]
    exact map_one θ
  have hθ'inv : ∀ a ∈ Z, θ' a⁻¹ = (θ' a)⁻¹ := fun a ha => by
    rw [hθ' _ (Z.inv_mem ha), hθ' _ ha]
    exact map_inv θ ⟨a, ha⟩
  have hθ'c₀ : θ' (x₀ * u₀ * x₀⁻¹ * u₀⁻¹) ≠ 1 := by
    rw [hθ' _ hc₀Z]
    exact hθ
  let K : Subgroup G :=
    { carrier := {u | u ∈ Q ∧ ∀ x ∈ X, θ' (x * u * x⁻¹ * u⁻¹) = 1}
      one_mem' := ⟨Q.one_mem, fun x _ => by
        rw [show x * 1 * x⁻¹ * (1 : G)⁻¹ = 1 by group]
        exact hθ'one⟩
      mul_mem' := fun {u u'} hu hu' => ⟨Q.mul_mem hu.1 hu'.1, fun x hx => by
        rw [hmulR x hx u hu.1 u' hu'.1, hθ'mul _ (hXQ x hx u hu.1) _ (hXQ x hx u' hu'.1),
          hu.2 x hx, hu'.2 x hx, one_mul]⟩
      inv_mem' := fun {u} hu => ⟨Q.inv_mem hu.1, fun x hx => by
        rw [hinvR x hx u hu.1, hθ'inv _ (hXQ x hx u hu.1), hu.2 x hx, inv_one]⟩ }
  have hYK : Q ⊓ Subgroup.centralizer (X : Set G) ≤ K := fun u hu => by
    obtain ⟨huQ, huC⟩ := Subgroup.mem_inf.mp hu
    refine ⟨huQ, fun x hx => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp huC x hx
    rw [show x * u * x⁻¹ * u⁻¹ = 1 by rw [h]; group]
    exact hθ'one
  have hKQ : K ≤ Q := fun u hu => hu.1
  have hKN : IsNormalIn L Q K := by
    refine ⟨hKQ, fun g hg u hu => ⟨hstep.1.2 g hg u hu.1, fun x hx => ?_⟩⟩
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (hLX (L.inv_mem hg)) x).mp hx
      rwa [inv_inv] at this
    obtain ⟨c, hcdef⟩ : ∃ c, c = (g⁻¹ * x * g) * u * (g⁻¹ * x * g)⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hcZ : c ∈ Z := hcdef ▸ hXQ _ hx' u hu.1
    have hgc : g * c * g⁻¹ = c := by
      have h := Subgroup.mem_centralizer_iff.mp (hLZ hg) c hcZ
      calc g * c * g⁻¹ = c * g * g⁻¹ := by rw [h]
        _ = c := by group
    rw [show x * (g * u * g⁻¹) * x⁻¹ * (g * u * g⁻¹)⁻¹ = g * c * g⁻¹ by rw [hcdef]; group, hgc,
      hcdef]
    exact hu.2 _ hx'
  have hu₀K : u₀ ∉ K := fun h => hθ'c₀ (h.2 x₀ hx₀)
  have hKY : K = Q ⊓ Subgroup.centralizer (X : Set G) := by
    rcases hstep.2.2.2 K hKN hYK hKQ with h | h
    · exact h
    · exact absurd (by rw [h]; exact hu₀Q) hu₀K
  set E := Q ⊓ Subgroup.centralizer (J : Set G) with hEdef
  have hEQ : E ≤ Q := inf_le_left
  have hNn : (J.subgroupOf X).Normal :=
    ⟨fun n _ g => by
      have h : g * n * g⁻¹ = n := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hXc g g.2 n n.2]
        group)
      rwa [h]⟩
  let ψ : ↥E → (↥X →* Multiplicative (ZMod 2)) := fun e =>
    { toFun := fun x => θ' ((x : G) * e * (x : G)⁻¹ * (e : G)⁻¹)
      map_one' := by
        simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel]
        exact hθ'one
      map_mul' := fun x x' => by
        simp only [Subgroup.coe_mul]
        rw [hmulL x x.2 x' x'.2 e (hEQ e.2),
          hθ'mul _ (hXQ _ x.2 _ (hEQ e.2)) _ (hXQ _ x'.2 _ (hEQ e.2))] }
  have hψJ : ∀ e : ↥E, ∀ x ∈ J.subgroupOf X, ψ e x = 1 := fun e x hx => by
    show θ' ((x : G) * e * (x : G)⁻¹ * (e : G)⁻¹) = 1
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp e.2).2 x
      (Subgroup.mem_subgroupOf.mp hx)
    rw [show (x : G) * e * (x : G)⁻¹ * (e : G)⁻¹ = 1 by rw [h]; group]
    exact hθ'one
  let Φ : ↥E →* (↥X ⧸ J.subgroupOf X →* Multiplicative (ZMod 2)) :=
    { toFun := fun e => QuotientGroup.lift (J.subgroupOf X) (ψ e) (hψJ e)
      map_one' := QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => by
        show θ' ((x : G) * ((1 : ↥E) : G) * (x : G)⁻¹ * ((1 : ↥E) : G)⁻¹) = 1
        simp only [OneMemClass.coe_one, mul_one, inv_one, mul_inv_cancel]
        exact hθ'one)
      map_mul' := fun e e' => QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => by
        show θ' ((x : G) * ((e * e' : ↥E) : G) * (x : G)⁻¹ * ((e * e' : ↥E) : G)⁻¹) =
          θ' ((x : G) * e * (x : G)⁻¹ * (e : G)⁻¹) * θ' ((x : G) * e' * (x : G)⁻¹ * (e' : G)⁻¹)
        rw [Subgroup.coe_mul, hmulR x x.2 e (hEQ e.2) e' (hEQ e'.2),
          hθ'mul _ (hXQ _ x.2 _ (hEQ e.2)) _ (hXQ _ x.2 _ (hEQ e'.2))]) }
  have hker : Φ.ker = (Q ⊓ Subgroup.centralizer (X : Set G)).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hKY]
    constructor
    · intro h
      refine ⟨hEQ e.2, fun x hx => ?_⟩
      have := DFunLike.congr_fun h ((⟨x, hx⟩ : ↥X) : ↥X ⧸ J.subgroupOf X)
      exact this
    · intro h
      exact QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun x => h.2 x x.2)
  haveI := CFSG.EvenSporadicStandard.TwoB.RankLemma.finite_hom (↥X ⧸ J.subgroupOf X)
  calc (Q ⊓ Subgroup.centralizer (X : Set G)).relIndex E = Φ.ker.index := by rw [hker]; rfl
    _ = Nat.card Φ.range := Subgroup.index_ker Φ
    _ ≤ Nat.card (↥X ⧸ J.subgroupOf X →* Multiplicative (ZMod 2)) :=
        Subgroup.card_le_card_group _
    _ ≤ Nat.card (↥X ⧸ J.subgroupOf X) :=
        CFSG.EvenSporadicStandard.TwoB.RankLemma.card_hom_le_card _
    _ = J.relIndex X := rfl

private theorem eq_or_eq_two_mul_of_two_pow_sub_one_dvd {n j : ℕ} (hn : 0 < n)
    (hdvd : 2 ^ n - 1 ∣ 2 ^ j - 1) (hlo : 2 ^ n ≤ 2 ^ j) (hhi : 2 ^ j ≤ 2 ^ n * 2 ^ n) :
    j = n ∨ j = 2 * n := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 n j
  rw [Nat.gcd_eq_left hdvd] at hg
  have h1 : 2 ^ Nat.gcd n j = 2 ^ n := by
    have := Nat.one_le_two_pow (n := n)
    have := Nat.one_le_two_pow (n := Nat.gcd n j)
    omega
  have h2 : Nat.gcd n j = n := Nat.pow_right_injective le_rfl h1
  have hdj : n ∣ j := h2 ▸ Nat.gcd_dvd_right n j
  have hnj : n ≤ j := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega
  have hj2 : j ≤ 2 * n := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    rw [two_mul, pow_add] at this
    omega
  obtain ⟨c, rfl⟩ := hdj
  have hc2 : c ≤ 2 := by
    by_contra h
    push Not at h
    have : n * 3 ≤ n * c := Nat.mul_le_mul_left n h
    omega
  have hc1 : 1 ≤ c := by
    by_contra h
    push Not at h
    interval_cases c
    omega
  interval_cases c
  · left; ring
  · right; ring

private theorem mem_conjugate_inf_centralizer_iff (Q X : Subgroup G) (g z : G) :
    z ∈ CFSG.conjugate (Q ⊓ Subgroup.centralizer (X : Set G)) g ↔
      z ∈ CFSG.conjugate Q g ∧ z ∈ Subgroup.centralizer (CFSG.conjugate X g : Set G) := by
  rw [CFSG.mem_conjugate_iff, Subgroup.mem_inf, CFSG.mem_conjugate_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
    rw [SetLike.mem_coe, CFSG.mem_conjugate_iff] at ht
    have h' := Subgroup.mem_centralizer_iff.mp h _ ht
    calc t * z = g⁻¹ * ((g * t * g⁻¹) * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * t * g⁻¹)) * g := by rw [h']
      _ = z * t := by group
  · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hx' : g⁻¹ * x * g ∈ CFSG.conjugate X g := by
      rw [CFSG.mem_conjugate_iff]
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    have h' := Subgroup.mem_centralizer_iff.mp h _ hx'
    calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [h']
      _ = g * z * g⁻¹ * x := by group

theorem str83G4_q2_inf_centralizer_le_conjugate_q1
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) :
    Q2 L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) ≤
      CFSG.conjugate (Q1 L1 L2 S) d.w := by
  intro z hz
  obtain ⟨hzQ2, hzC⟩ := Subgroup.mem_inf.mp hz
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hz' : d.w * z * d.w⁻¹ ∈ Q2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P2 L1 L2 S) (hL2P d.hwH2)) z).mp
      hzQ2
  have hCX : d.w * z * d.w⁻¹ ∈ Subgroup.centralizer (str83X L1 L2 S : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    have hxw : d.w⁻¹ * x * d.w ∈ CFSG.conjugate (str83X L1 L2 S) d.w := by
      rw [CFSG.mem_conjugate_iff]
      rwa [show d.w * (d.w⁻¹ * x * d.w) * d.w⁻¹ = x by group]
    have h := Subgroup.mem_centralizer_iff.mp hzC _ hxw
    calc x * (d.w * z * d.w⁻¹) = d.w * ((d.w⁻¹ * x * d.w) * z) * d.w⁻¹ := by group
      _ = d.w * (z * (d.w⁻¹ * x * d.w)) * d.w⁻¹ := by rw [h]
      _ = d.w * z * d.w⁻¹ * x := by group
  rw [CFSG.mem_conjugate_iff]
  exact (Subgroup.mem_inf.mp (str83G4_centralizer_x_le hfr (str83G4_not_le_normalizer_z2 hfr)
    (Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right (str83G4_q2_le_s hfr hz'), hCX⟩))).1

theorem str83G4_mul_self_mem_centralizer_conjugate_x
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) {y : G}
    (hy : y ∈ str83Y L1 L2 S) :
    y * y ∈ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun t ht => ?_
  have hc : y * t * y⁻¹ * t⁻¹ ∈ str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w := by
    have := str83G4_commutator_y_conjugate_x_le hfr d hX hB
      (Subgroup.commutator_mem_commutator hy ht)
    rwa [commutatorElement_def] at this
  obtain ⟨c, hcdef⟩ : ∃ c, c = y * t * y⁻¹ * t⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hcX : c ∈ str83X L1 L2 S := (Subgroup.mem_inf.mp hc).1
  have hyc : c * y = y * c := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 c hcX
  have hcc : c * c = 1 := by simpa [sq] using hX.2 c hcX
  have hyt : y * t * y⁻¹ = c * t := by
    rw [hcdef]
    group
  have hyc' : y * c * y⁻¹ = c := by
    calc y * c * y⁻¹ = c * y * y⁻¹ := by rw [hyc]
      _ = c := by group
  have h : (y * y) * t * (y * y)⁻¹ = t := by
    calc (y * y) * t * (y * y)⁻¹ = y * (y * t * y⁻¹) * y⁻¹ := by group
      _ = y * (c * t) * y⁻¹ := by rw [hyt]
      _ = (y * c * y⁻¹) * (y * t * y⁻¹) := by group
      _ = c * (c * t) := by rw [hyc', hyt]
      _ = t := by rw [← mul_assoc, hcc, one_mul]
  calc t * (y * y) = ((y * y) * t * (y * y)⁻¹) * (y * y) := by rw [h]
    _ = y * y * t := by group

theorem str83G4_conjugate_y_le_conjugate_x_sup_q1
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    CFSG.conjugate (str83Y L1 L2 S) d.w ≤ CFSG.conjugate (str83X L1 L2 S) d.w ⊔ Q1 L1 L2 S := by
  intro z hz
  rw [CFSG.mem_conjugate_iff] at hz
  obtain ⟨y, hydef⟩ : ∃ y, y = d.w * z * d.w⁻¹ := ⟨_, rfl⟩
  rw [← hydef] at hz
  have hzy : z = d.w⁻¹ * y * d.w := by
    rw [hydef]
    group
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hwP : d.w ∈ P2 L1 L2 S := hL2P d.hwH2
  have hw2 : d.w * d.w ∈ Q2 L1 L2 S := str83G4_w_mul_self_mem_q2 hfr d
  have hw2P : (d.w * d.w)⁻¹ ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr ((Q2 L1 L2 S).inv_mem hw2)))
  have hyQ2 : y ∈ Q2 L1 L2 S := str83G4_y_le_q2 hfr hz
  have hzQ2 : z ∈ Q2 L1 L2 S := by
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P2 L1 L2 S)
      ((P2 L1 L2 S).inv_mem hwP)) y).mp hyQ2
    rwa [inv_inv, ← hzy] at this
  have hyy : d.w * (y * y) * d.w⁻¹ ∈ Q1 L1 L2 S := by
    have := str83G4_q2_inf_centralizer_le_conjugate_q1 hfr d (Subgroup.mem_inf.mpr
      ⟨(Q2 L1 L2 S).mul_mem hyQ2 hyQ2, str83G4_mul_self_mem_centralizer_conjugate_x hfr d hX hB hz⟩)
    rwa [CFSG.mem_conjugate_iff] at this
  rw [str83G4_mem_conjugate_x_sup_q1_iff hfr d hX hB]
  refine ⟨str83G4_q2_le_s hfr hzQ2, ?_⟩
  have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hw2P) _).mp hyy
  rwa [show (d.w * d.w)⁻¹ * (d.w * (y * y) * d.w⁻¹) * (d.w * d.w)⁻¹⁻¹ = z ^ 2 by
    rw [hzy, sq]; group] at h

theorem str83G4_relIndex_x_y_eq_mul
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIX : (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w).relIndex (str83X L1 L2 S) =
      (2 ^ (2 * a + 1)) ^ 2)
    (hQstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S))
    (hfpf : ∀ k ∈ d.D1, k ≠ 1 → ∀ x ∈ str83X L1 L2 S,
      k * x * k⁻¹ * x⁻¹ ∈ Z1 L1 L2 S → x ∈ Z1 L1 L2 S) :
    ∃ ε : ℕ, (ε = 1 ∨ ε = 2 ^ (2 * a + 1)) ∧
      (str83X L1 L2 S).relIndex (str83Y L1 L2 S) =
        ε * (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w).relIndex
          (str83Y L1 L2 S ⊓
            Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G)) := by
  classical
  have hD1card : Nat.card d.D1 = 2 ^ (2 * a + 1) - 1 := by
    obtain ⟨hF, -, ha, ⟨eSz⟩, -, -⟩ := hfr
    have hBT : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
      BenderType.suzuki a ha (eSz.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
    exact (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow d.hD1hall d.hD1sup hBT).1
  have hY1 := str83G4_conjugate_y_le_conjugate_x_sup_q1 hfr d hX hB
  have hrelVXw := str83G4_relIndex_conjugate_x_inf_q1 hfr d hX hB
  set q := 2 ^ (2 * a + 1) with hq
  have hqpos : 0 < q := Nat.two_pow_pos _
  set X := str83X L1 L2 S with hXdef
  set Xw := CFSG.conjugate X d.w with hXwdef
  set Q := Q1 L1 L2 S with hQdef
  set Y := str83Y L1 L2 S with hYdef
  set Yw := CFSG.conjugate Y d.w with hYwdef
  set I := X ⊓ Xw with hIdef
  set Y0 := Y ⊓ Subgroup.centralizer (Xw : Set G) with hY0def
  set T := Yw ⊓ Q with hTdef
  set V := Xw ⊓ Q with hVdef
  set M := T ⊔ Y with hMdef
  have hXY : X ≤ Y := str83X_le_str83Y hfr hX
  have hYQ : Y ≤ Q := inf_le_left
  have hXQ : X ≤ Q := str83X_le_q1 hfr
  have hL2P : L2 ⊔ S ≤ P2 L1 L2 S :=
    sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hwP : d.w ∈ P2 L1 L2 S := hL2P d.hwH2
  have hw2P : d.w * d.w ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr (str83G4_w_mul_self_mem_q2 hfr d)))
  have hQP : Q ≤ P1 L1 L2 S := fun z hz => (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
    ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q1_le_s hfr hz))
  have hNY : ∀ g ∈ P1 L1 L2 S, g ∈ Subgroup.normalizer (Y : Set G) := fun g hg =>
    A4.mem_normalizer_inf (le_normalizer_pCoreOf 2 (P1 L1 L2 S) hg)
      (F7.normalizer_le_normalizer_centralizer _ (le_normalizer_str83X L1 L2 S hg))
  have hYwmem : ∀ z, z ∈ Yw ↔
      z ∈ CFSG.conjugate Q d.w ∧ z ∈ Subgroup.centralizer (Xw : Set G) :=
    fun z => mem_conjugate_inf_centralizer_iff Q X d.w z
  have hYwC : Yw ≤ Subgroup.centralizer (Xw : Set G) := fun z hz => ((hYwmem z).mp hz).2
  have hXwYw : Xw ≤ Yw := fun z hz => by
    rw [hYwdef, CFSG.mem_conjugate_iff]
    rw [hXwdef, CFSG.mem_conjugate_iff] at hz
    exact hXY hz
  have hYwQ2 : Yw ≤ Q2 L1 L2 S := fun z hz => by
    rw [hYwdef, CFSG.mem_conjugate_iff] at hz
    have h := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (P2 L1 L2 S)
      ((P2 L1 L2 S).inv_mem hwP)) _).mp (str83G4_y_le_q2 hfr hz)
    rwa [inv_inv, show d.w⁻¹ * (d.w * z * d.w⁻¹) * d.w = z by group] at h
  have hX2mem : ∀ z, d.w * (d.w * z * d.w⁻¹) * d.w⁻¹ ∈ X ↔ z ∈ X := fun z => by
    rw [show d.w * (d.w * z * d.w⁻¹) * d.w⁻¹ = (d.w * d.w) * z * (d.w * d.w)⁻¹ by group]
    exact ((Subgroup.mem_normalizer_iff.mp (le_normalizer_str83X L1 L2 S hw2P)) z).symm
  have hIw : CFSG.conjugate I d.w = I := by
    ext z
    rw [CFSG.mem_conjugate_iff, Subgroup.mem_inf, Subgroup.mem_inf, hXwdef,
      CFSG.mem_conjugate_iff, CFSG.mem_conjugate_iff, hX2mem]
    exact and_comm
  have hXwN : Xw ≤ Subgroup.normalizer (Q : Set G) := fun t ht =>
    le_normalizer_pCoreOf 2 (P1 L1 L2 S) ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      ((le_sup_right : S ≤ bigB L1 L2 S) (str83G4_q2_le_s hfr (hYwQ2 (hXwYw ht)))))
  have hYweq : Yw = T ⊔ Xw := by
    refine le_antisymm (fun z hz => ?_) (sup_le inf_le_left hXwYw)
    have hz' : z ∈ Q ⊔ Xw := by
      rw [sup_comm]
      exact hY1 hz
    obtain ⟨u, hu, t, ht, hut⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hXwN).mp hz'
    have huYw : u ∈ Yw := by
      rw [show u = z * t⁻¹ by rw [hut]; group]
      exact Yw.mul_mem hz (Yw.inv_mem (hXwYw ht))
    rw [hut]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨huYw, hu⟩) ht
  have hTXw : T ≤ Subgroup.normalizer (Xw : Set G) :=
    (inf_le_left.trans hYwC).trans (Subgroup.centralizer_le_normalizer _)
  have hrelYX : X.relIndex Y = V.relIndex T := by
    have h1 : Xw.relIndex Yw = X.relIndex Y :=
      Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹) X Y
    have h2 : Xw.relIndex (T ⊔ Xw) = Xw.relIndex T := relIndex_sup_left_of_le_normalizer hTXw
    have h3 : Xw ⊓ T = V := by
      ext z
      simp only [Subgroup.mem_inf, hTdef, hVdef]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hXwYw h.1, h.2⟩⟩
    rw [← h1, hYweq, h2, ← Subgroup.inf_relIndex_right, h3]
  have hIV : I ≤ V := fun z hz =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).2, hXQ (Subgroup.mem_inf.mp hz).1⟩
  have hVT : V ≤ T := inf_le_inf_right Q hXwYw
  have hrelIXw : I.relIndex Xw = q ^ 2 := by
    have h : (CFSG.conjugate I d.w).relIndex Xw = I.relIndex X :=
      Subgroup.relIndex_pointwise_smul (MulAut.conj d.w⁻¹) I X
    rw [hIw] at h
    rw [h, hIX]
  have hrelIV : I.relIndex V = q := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ hIV (inf_le_left : V ≤ Xw)
    rw [hrelVXw, hrelIXw, sq] at h
    exact Nat.eq_of_mul_eq_mul_right hqpos h
  have hY0Yw : Y0 ≤ Yw := fun z hz => by
    obtain ⟨hzY, hzC⟩ := Subgroup.mem_inf.mp hz
    exact (hYwmem z).mpr ⟨str83G4_q2_inf_centralizer_le_conjugate_q1 hfr d
      (Subgroup.mem_inf.mpr ⟨str83G4_y_le_q2 hfr hzY, hzC⟩), hzC⟩
  have hY0T : Y0 ≤ T := fun z hz =>
    Subgroup.mem_inf.mpr ⟨hY0Yw hz, hYQ (Subgroup.mem_inf.mp hz).1⟩
  have hYT : Y ⊓ T = Y0 := by
    refine le_antisymm (fun z hz => ?_) (le_inf inf_le_left hY0T)
    obtain ⟨hzY, hzT⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨hzY, hYwC (Subgroup.mem_inf.mp hzT).1⟩
  have hIY0 : I ≤ Y0 := fun z hz => by
    obtain ⟨hzX, hzXw⟩ := Subgroup.mem_inf.mp hz
    exact Subgroup.mem_inf.mpr ⟨hXY hzX, hYwC (hXwYw hzXw)⟩
  have hTN : T ≤ Subgroup.normalizer (Y : Set G) := fun z hz =>
    hNY z (hQP (Subgroup.mem_inf.mp hz).2)
  have hrelTY0 : Y0.relIndex T = Y.relIndex M := by
    rw [← hYT, Subgroup.inf_relIndex_right, hMdef, relIndex_sup_left_of_le_normalizer hTN]
  have hstar : q * X.relIndex Y = I.relIndex Y0 * Y.relIndex M := by
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ hIV hVT
    have h2 := Subgroup.relIndex_mul_relIndex _ _ _ hIY0 hY0T
    rw [hrelIV, ← hrelYX] at h1
    rw [hrelTY0] at h2
    exact h1.trans h2.symm
  have hXY0 : X ⊓ Y0 = I := by
    rw [hY0def, ← inf_assoc, inf_eq_left.mpr hXY, hXI]
  have hXYne : X.relIndex Y ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hY0le : I.relIndex Y0 ≤ X.relIndex Y := by
    rw [← hXY0, Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_le_of_le_right inf_le_left hXYne
  have hA : 0 < X.relIndex Y := Nat.pos_of_ne_zero hXYne
  have hMlo : q ≤ Y.relIndex M := by
    by_contra h
    push Not at h
    nlinarith [hstar, hY0le, hA, h, Nat.zero_le (Y.relIndex M)]
  have hMQ : M ≤ Q := sup_le inf_le_right hYQ
  have hMCI : M ≤ Q ⊓ Subgroup.centralizer (I : Set G) := by
    refine sup_le (le_inf inf_le_right ?_) (le_inf hYQ ?_)
    · exact (inf_le_left.trans hYwC).trans (Subgroup.centralizer_le inf_le_right)
    · exact (inf_le_right : Y ≤ Subgroup.centralizer (X : Set G)).trans
        (Subgroup.centralizer_le inf_le_left)
  have hMup : Y.relIndex M ≤ q ^ 2 := by
    have hG2 := relIndex_inf_centralizer_le_of_isChiefStep (L := L1 ⊔ S) (X := X)
      (Z := Z1 L1 L2 S) (Q := Q) (J := I) hX (str83G4_z1_le_x hfr) (fun x hx u hu => by
        have := str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hu)
        rwa [commutatorElement_def] at this)
      ((str83G4_q1_le_s hfr).trans (le_sup_right.trans (str83G4_sup_le_centralizer_z1 hfr)))
      (str83G4_sup_le_centralizer_z1 hfr) (str83G4_sup_le_normalizer_x hfr) hQstep
    calc Y.relIndex M ≤ Y.relIndex (Q ⊓ Subgroup.centralizer (I : Set G)) :=
          Subgroup.relIndex_le_of_le_right hMCI Subgroup.index_ne_zero_of_finite
      _ ≤ I.relIndex X := hG2
      _ = q ^ 2 := hIX
  have hD1L : ∀ k ∈ d.D1, k ∈ L1 ⊔ S := fun k hk =>
    Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 hk))
  have hD1P : ∀ k ∈ d.D1, k ∈ P1 L1 L2 S := fun k hk =>
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S)
      (str83G4Data_sup_le_bigB d (Subgroup.mem_sup_left hk))
  have hYweq' : Yw = CFSG.conjugate Q d.w ⊓ Subgroup.centralizer (Xw : Set G) := by
    ext z
    rw [Subgroup.mem_inf]
    exact hYwmem z
  have hD1N := str83G4_d1_sup_d2_le_normalizer hfr d
  have hD1Yw : ∀ k ∈ d.D1, k ∈ Subgroup.normalizer (Yw : Set G) := fun k hk => by
    rw [hYweq']
    exact A4.mem_normalizer_inf (hD1N.1 (Subgroup.mem_sup_left hk))
      (F7.normalizer_le_normalizer_centralizer _ (hD1N.2.1 (Subgroup.mem_sup_left hk)))
  have hD1M : d.D1 ≤ Subgroup.normalizer (M : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_sup T Y (Subgroup.mem_inf.mpr
      ⟨A4.mem_normalizer_inf (hD1Yw k hk) (le_normalizer_pCoreOf 2 (P1 L1 L2 S) (hD1P k hk)),
        hNY k (hD1P k hk)⟩)
  have hD1Y : d.D1 ≤ Subgroup.normalizer (Y : Set G) := fun k hk => hNY k (hD1P k hk)
  have hfix : ∀ k ∈ d.D1, k ≠ 1 → ∀ m ∈ M, k * m * k⁻¹ = m → m ∈ Y := by
    intro k hk hk1 m hm hkm
    have hmQ : m ∈ Q := hMQ hm
    have hmC := mem_centralizer_of_conj_eq_of_fpf hX (str83G4_z1_le_x hfr)
      (str83G4_sup_le_centralizer_z1 hfr (hD1L k hk))
      (str83G4_sup_le_normalizer_x hfr (hD1L k hk))
      (Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hk)) (hfpf k hk hk1)
      (fun x hx => by
        have := str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hmQ)
        rwa [commutatorElement_def] at this)
      ((str83G4_q1_le_s hfr).trans (le_sup_right.trans (str83G4_sup_le_centralizer_z1 hfr)) hmQ)
      hkm
    exact Subgroup.mem_inf.mpr ⟨hmQ, hmC⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 (P1 L1 L2 S)
  obtain ⟨k₁, hk₁⟩ := IsPGroup.iff_card.mp (hQp.to_le hYQ)
  have hcop : Nat.Coprime (Nat.card d.D1) (Nat.card Y) := by
    rw [hk₁]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h2 => ?_))
    obtain ⟨m, hm⟩ := d.hD1hall.2.1
    obtain ⟨c, hc⟩ := h2
    omega
  have hdvd := card_dvd_relIndex_sub_one_of_fixed_mem (le_sup_right : Y ≤ M) hD1M hD1Y hfix hcop
  rw [hD1card] at hdvd
  obtain ⟨k₂, hk₂⟩ := IsPGroup.iff_card.mp (hQp.to_le hMQ)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hk₂ ▸ Subgroup.relIndex_dvd_card (H := Y) (K := M))
  rw [hj] at hdvd hMlo hMup hstar
  have hjn := eq_or_eq_two_mul_of_two_pow_sub_one_dvd (by omega : 0 < 2 * a + 1) hdvd hMlo
    (by rw [← sq]; exact hMup)
  rcases hjn with rfl | rfl
  · refine ⟨1, Or.inl rfl, Nat.eq_of_mul_eq_mul_left hqpos ?_⟩
    calc q * X.relIndex Y = I.relIndex Y0 * q := hstar
      _ = q * (1 * I.relIndex Y0) := by rw [one_mul, mul_comm]
  · refine ⟨q, Or.inr rfl, Nat.eq_of_mul_eq_mul_left hqpos ?_⟩
    have h2n : 2 ^ (2 * (2 * a + 1)) = q * q := by
      show 2 ^ (2 * (2 * a + 1)) = 2 ^ (2 * a + 1) * 2 ^ (2 * a + 1)
      rw [← pow_add]
      congr 1
      ring
    calc q * X.relIndex Y = I.relIndex Y0 * 2 ^ (2 * (2 * a + 1)) := hstar
      _ = q * (q * I.relIndex Y0) := by rw [h2n]; ring

theorem str83G4_relIndex_x_y_eq_one_or
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S)
    (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S)
    (hXI : str83X L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w)
    (hIX : (str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w).relIndex (str83X L1 L2 S) =
      (2 ^ (2 * a + 1)) ^ 2)
    (hQstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) (str83Y L1 L2 S) (Q1 L1 L2 S))
    (hfpf : ∀ k ∈ d.D1, k ≠ 1 → ∀ x ∈ str83X L1 L2 S,
      k * x * k⁻¹ * x⁻¹ ∈ Z1 L1 L2 S → x ∈ Z1 L1 L2 S)
    (hYB : str83Y L1 L2 S ⊓ Subgroup.centralizer (CFSG.conjugate (str83X L1 L2 S) d.w : Set G) =
      str83X L1 L2 S ⊓ CFSG.conjugate (str83X L1 L2 S) d.w) :
    (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 1 ∨
      (str83X L1 L2 S).relIndex (str83Y L1 L2 S) = 2 ^ (2 * a + 1) := by
  obtain ⟨ε, hε, h⟩ := str83G4_relIndex_x_y_eq_mul hfr d hX hB hXI hIX hQstep hfpf
  rw [hYB, Subgroup.relIndex_self, mul_one] at h
  rcases hε with rfl | rfl
  · exact Or.inl h
  · exact Or.inr h

end CFSG.Quasithin.Stroth

end
