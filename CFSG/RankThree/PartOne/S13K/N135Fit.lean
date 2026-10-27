module

public import CFSG.RankThree.PartOne.S13K.N135Nil
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.FeitThompson.OddOrderTheorem

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K.N135

variable {V : Type} [CommGroup V]

theorem eq_bot_of_pgroup_normal [Finite V] {p : ℕ} [hpp : Fact p.Prime]
    (hcard : Nat.card V = p ^ 4) {W P : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ w ∈ W, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤)
    (hPn : ∀ w ∈ W, ∀ x ∈ P, w * x * w⁻¹ ∈ P) (hP : IsPGroup p P) : P = ⊥ := by
  let T : Subgroup V :=
    { carrier := {v | ∀ x ∈ P, x v = v}
      mul_mem' := fun {a b} ha hb x hx => by rw [map_mul, ha x hx, hb x hx]
      one_mem' := fun x _ => map_one x
      inv_mem' := fun {a} ha x hx => by rw [map_inv, ha x hx] }
  have hTinv : ∀ w ∈ W, ∀ s ∈ T, w s ∈ T := by
    intro w hw s hs x hx
    have hx' : w⁻¹ * x * w ∈ P := by
      have := hPn w⁻¹ (W.inv_mem hw) x hx
      rwa [inv_inv] at this
    have h2 : w⁻¹ (x (w s)) = s := hs _ hx'
    have h3 := congrArg w h2
    rwa [MulAut.apply_inv_self] at h3
  have hTne : T ≠ ⊥ := by
    intro hbot
    have h1 := hP.card_modEq_card_fixedPoints V
    have h2 : Nat.card (MulAction.fixedPoints P V) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨⟨1, ?_⟩⟩⟩
      · have ha : (a : V) ∈ T := fun x hx => by
          have := (MulAction.mem_fixedPoints.1 a.2) ⟨x, hx⟩
          exact this
        have hb : (b : V) ∈ T := fun x hx => by
          have := (MulAction.mem_fixedPoints.1 b.2) ⟨x, hx⟩
          exact this
        rw [hbot, Subgroup.mem_bot] at ha hb
        exact Subtype.ext (ha.trans hb.symm)
      · exact MulAction.mem_fixedPoints.2 fun m => map_one (m : MulAut V)
    rw [h2, hcard] at h1
    have h3 : p ∣ 1 := by
      have h4 : p ^ 4 ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 (dvd_pow_self p (by norm_num))
      exact Nat.modEq_zero_iff_dvd.1 (h1.symm.trans h4)
    exact hpp.out.one_lt.ne' (Nat.dvd_one.1 h3)
  have hTtop : T = ⊤ := (hirr T hTinv).resolve_left hTne
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ T := by rw [hTtop]; trivial
  rw [MulAut.one_apply]
  exact hv x hx

theorem not_dvd_orderOf [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hcard : Nat.card V = p ^ 4)
    {W F : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ w ∈ W, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤)
    (hFn : ∀ w ∈ W, ∀ x ∈ F, w * x * w⁻¹ ∈ F) [Group.IsNilpotent F] :
    ∀ z ∈ F, ¬ p ∣ orderOf z := by
  intro z hz hpz
  have : Finite (MulAut V) :=
    Finite.of_injective (fun φ : MulAut V => (φ : V → V)) (fun a b h => MulEquiv.ext (congrFun h))
  obtain ⟨P⟩ : Nonempty (Sylow p F) := inferInstance
  have hPn : (P : Subgroup F).Normal := inferInstance
  have huniq : Unique (Sylow p F) := Sylow.unique_of_normal P hPn
  let P' : Subgroup (MulAut V) := (P : Subgroup F).map F.subtype
  have hP'p : IsPGroup p P' := P.2.map F.subtype
  have hmem : ∀ x : F, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ (P : Subgroup F) := by
    intro x ⟨k, hk⟩
    have hzp : IsPGroup p (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    have hQP : Q = P := Subsingleton.elim Q P
    rw [hQP] at hQ
    exact hQ (Subgroup.mem_zpowers x)
  have hP'n : ∀ w ∈ W, ∀ y ∈ P', w * y * w⁻¹ ∈ P' := by
    intro w hw y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hF' : w * (x : MulAut V) * w⁻¹ ∈ F := hFn w hw x x.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.2) ⟨x, hx⟩
    refine Subgroup.mem_map.2 ⟨⟨_, hF'⟩, hmem _ ⟨k, ?_⟩, rfl⟩
    have h1 : orderOf (⟨w * (x : MulAut V) * w⁻¹, hF'⟩ : F) = orderOf (w * (x : MulAut V) * w⁻¹) :=
      (Subgroup.orderOf_coe (⟨w * (x : MulAut V) * w⁻¹, hF'⟩ : F)).symm
    have h2 : orderOf (w * (x : MulAut V) * w⁻¹) = orderOf (x : MulAut V) :=
      MulEquiv.orderOf_eq (MulAut.conj w) (x : MulAut V)
    have h3 : orderOf (x : MulAut V) = orderOf x := (Subgroup.orderOf_coe x)
    have h4 : orderOf (⟨x, hx⟩ : (P : Subgroup F)) = orderOf x :=
      (Subgroup.orderOf_coe (⟨x, hx⟩ : (P : Subgroup F))).symm
    rw [h1, h2, h3, ← h4]
    exact hk
  have hP'bot : P' = ⊥ := eq_bot_of_pgroup_normal hcard hirr hP'n hP'p
  have hz0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have hz1 : orderOf (z ^ (orderOf z / p)) = p := orderOf_pow_orderOf_div hz0 hpz
  have hz1F : z ^ (orderOf z / p) ∈ F := F.pow_mem hz _
  have hz1P : (⟨z ^ (orderOf z / p), hz1F⟩ : F) ∈ (P : Subgroup F) := by
    refine hmem _ ⟨1, ?_⟩
    rw [pow_one]
    have : orderOf (⟨z ^ (orderOf z / p), hz1F⟩ : F) = orderOf (z ^ (orderOf z / p)) :=
      (Subgroup.orderOf_coe (⟨z ^ (orderOf z / p), hz1F⟩ : F)).symm
    rw [this, hz1]
  have hz1P' : z ^ (orderOf z / p) ∈ P' := Subgroup.mem_map.2 ⟨_, hz1P, rfl⟩
  rw [hP'bot, Subgroup.mem_bot] at hz1P'
  rw [hz1P', orderOf_one] at hz1
  exact hpp.out.one_lt.ne' hz1.symm

@[expose] def conjOn {G : Type*} [Group G] (N : Subgroup G) (w : G)
    (hw : ∀ n ∈ N, w * n * w⁻¹ ∈ N) (hw' : ∀ n ∈ N, w⁻¹ * n * w ∈ N) : MulAut N where
  toFun n := ⟨w * n * w⁻¹, hw n n.2⟩
  invFun n := ⟨w⁻¹ * n * w, hw' n n.2⟩
  left_inv n := Subtype.ext (by group)
  right_inv n := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem commute_of_normal_odd [Finite V] {p : ℕ} [hpp : Fact p.Prime] (hp2 : p ≠ 2)
    (hexp : ∀ v : V, v ^ p = 1) (hcard : Nat.card V = p ^ 4)
    {W Λ : Subgroup (MulAut V)} (hΛW : Λ ≤ W)
    (hirr : ∀ S : Subgroup V, (∀ w ∈ W, ∀ s ∈ S, w s ∈ S) → S = ⊥ ∨ S = ⊤)
    {u : MulAut V} (hu2 : u * u = 1) (huΛ : u ∈ Λ) (hucomm : ∀ g ∈ Λ, g * u = u * g)
    {c : V} (hc1 : c ≠ 1) (hΛc : ∀ g ∈ Λ, g c = c)
    (hfix : ∀ e, u e = e ↔ e ∈ Subgroup.zpowers c)
    (hfour : ∃ B₀ : Subgroup V, ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → S ≠ ⊥ → S ≠ ⊤ →
      S = Subgroup.zpowers c ∨ S = B₀)
    {N : Subgroup (MulAut V)} (hNn : ∀ w ∈ W, ∀ n ∈ N, w * n * w⁻¹ ∈ N)
    (hNodd : Odd (Nat.card N)) : ∀ n ∈ N, n * u = u * n := by
  have : Finite (MulAut V) :=
    Finite.of_injective (fun φ : MulAut V => (φ : V → V)) (fun a b h => MulEquiv.ext (congrFun h))
  have hsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd
  let F : Subgroup N := CFSG.fittingSubgroup N
  have hchar : ∀ φ : MulAut N, ∀ f ∈ F, φ f ∈ F := by
    intro φ f hf
    have h := (inferInstance : (CFSG.fittingSubgroup N).Characteristic).fixed φ
    have : f ∈ (CFSG.fittingSubgroup N).comap φ.toMonoidHom := by rw [h]; exact hf
    exact this
  let R : Subgroup (MulAut V) := F.map N.subtype
  have hWinv : ∀ w ∈ W, ∀ n ∈ N, w⁻¹ * n * w ∈ N := by
    intro w hw n hn
    have := hNn w⁻¹ (W.inv_mem hw) n hn
    rwa [inv_inv] at this
  have hRn : ∀ w ∈ W, ∀ r ∈ R, w * r * w⁻¹ ∈ R := by
    intro w hw r hr
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hr
    exact Subgroup.mem_map.2 ⟨conjOn N w (hNn w hw) (hWinv w hw) f, hchar _ f hf, rfl⟩
  have hRnil : Group.IsNilpotent R := by
    have e : F ≃* R := F.equivMapOfInjective N.subtype N.subtype_injective
    exact Group.nilpotent_of_mulEquiv e
  have hRodd : ∀ r ∈ R, Odd (orderOf r) := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hr
    have h1 : orderOf (N.subtype f) = orderOf f := Subgroup.orderOf_coe f
    show Odd (orderOf (N.subtype f))
    rw [h1]
    exact Odd.of_dvd_nat hNodd (orderOf_dvd_natCard f)
  have hfourc : ∀ S : Subgroup V, (∀ g ∈ Λ, ∀ s ∈ S, g s ∈ S) → c ∈ S →
      S = Subgroup.zpowers c ∨ S = ⊤ := by
    intro S hS hcS
    by_cases htop : S = ⊤
    · exact Or.inr htop
    · left
      have hbot : S ≠ ⊥ := fun h => hc1 (by rw [h] at hcS; exact Subgroup.mem_bot.1 hcS)
      obtain ⟨B₀, hB₀⟩ := hfour
      rcases hB₀ S hS hbot htop with h | h
      · exact h
      · exfalso
        have := vMinus_eq hp2 hexp hcard hu2 hc1 hfix hucomm hB₀
        rw [h, ← this] at hcS
        exact c_not_mem_vMinus hp2 hexp hc1 hfix hcS
  have hRab : ∀ ρ ∈ R, ∀ σ ∈ R, ρ * σ = σ * ρ :=
    comm_of_nilpotent_normal hexp hcard hΛW hirr hc1 hΛc hfourc hRn hRodd
  have hRp : ∀ z ∈ R, ¬ p ∣ orderOf z := not_dvd_orderOf hcard hirr hRn
  have hcomm : ∀ z ∈ R, z * u = u * z :=
    claimA hp2 hexp hcard hu2 hc1 hfix huΛ hucomm hfour hRab
      (fun g hg z hz => hRn g (hΛW hg) z hz) hRodd hRp
  have hu1 : ∀ n ∈ N, u * n * u⁻¹ ∈ N := hNn u (hΛW huΛ)
  have hu1' : ∀ n ∈ N, u⁻¹ * n * u ∈ N := hWinv u (hΛW huΛ)
  let φ : MulAut N := conjOn N u hu1 hu1'
  have hφ2 : φ ^ 2 = 1 := by
    have h1 : φ * φ = 1 := by
      refine MulEquiv.ext fun n => Subtype.ext ?_
      show u * (u * (n : MulAut V) * u⁻¹) * u⁻¹ = n
      have : u * (u * (n : MulAut V) * u⁻¹) * u⁻¹ = (u * u) * n * (u * u)⁻¹ := by group
      rw [this, hu2]
      group
    rw [sq]; exact h1
  have hfixed : ∀ x ∈ CFSG.fittingSubgroup N, φ x = x := by
    intro x hx
    refine Subtype.ext ?_
    show u * (x : MulAut V) * u⁻¹ = x
    have h1 : (x : MulAut V) * u = u * x := hcomm _ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    exact mul_inv_eq_iff_eq_mul.2 h1.symm
  have hcop : Nat.Coprime 2 (Nat.card (CFSG.fittingSubgroup N)) :=
    Nat.coprime_two_left.2 (Odd.of_dvd_nat hNodd (Subgroup.card_subgroup_dvd_card _))
  have hφ1 : φ = 1 := CFSG.mulAut_eq_one_of_fixes_fittingSubgroup N hsolv φ 2 hφ2 hcop hfixed
  intro n hn
  have h1 : u * n * u⁻¹ = n :=
    congrArg (fun m : MulAut N => ((m ⟨n, hn⟩ : N) : MulAut V)) hφ1
  exact (mul_inv_eq_iff_eq_mul.1 h1).symm

end CFSG.RankThree.PartOne.S13K.N135
