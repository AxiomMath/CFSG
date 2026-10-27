module

public import CFSG.Quasithin.Background.FFC5T8

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall Matrix

section T9

variable {V : Type} [CommGroup V]

@[expose] def NatQuot3.thetaA {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z) :
    Additive ↥U →+ (Fin 3 → ZMod 2) where
  toFun w := Multiplicative.toAdd (D.θ (Additive.toMul w))
  map_zero' := by simp
  map_add' x y := by simp

theorem NatQuot3.thetaA_equiv {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z)
    (hLU : ∀ g ∈ L, ∀ w ∈ U, g w ∈ U) (γ : SL3F2) (w : Additive ↥U) :
    D.thetaA (muW hLU (D.ρ γ) w) = muF2 3 γ (D.thetaA w) := by
  have h1 := D.equiv γ (Additive.toMul w)
  show Multiplicative.toAdd (D.θ (Additive.toMul (muW hLU (D.ρ γ) w))) =
    muF2 3 γ (Multiplicative.toAdd (D.θ (Additive.toMul w)))
  rw [muW_apply]
  exact congrArg Multiplicative.toAdd h1

theorem NatQuot3.thetaA_surj {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z) :
    Function.Surjective D.thetaA := by
  intro v
  obtain ⟨y, hy⟩ := D.θ_surj (Multiplicative.ofAdd v)
  exact ⟨Additive.ofMul y, by
    show Multiplicative.toAdd (D.θ y) = v
    rw [hy]; rfl⟩

theorem NatQuot3.thetaA_ker {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : NatQuot3 L U Z)
    (w : Additive ↥U) : D.thetaA w = 0 → ((Additive.toMul w : ↥U) : V) ∈ Z := fun hw =>
  (D.θ_ker _).1 (Multiplicative.toAdd.injective hw)

theorem cocyF_sub_coboundary {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W) (hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ W) (u : V)
    (m : Additive ↥W) (g : ↥L) :
    ((Additive.toMul (cocyF hc u g - (muW hLW g m - m)) : ↥W) : V) =
      (g : MulAut V) (u * (((Additive.toMul m : ↥W) : V))⁻¹) *
        (u * (((Additive.toMul m : ↥W) : V))⁻¹)⁻¹ := by
  rw [toMul_sub, Subgroup.coe_div, muW_sub_apply]
  show (g : MulAut V) u * u⁻¹ / ((g : MulAut V) ((Additive.toMul m : ↥W) : V) *
    ((Additive.toMul m : ↥W) : V)⁻¹) = _
  rw [map_mul, map_inv, div_eq_mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

end T9

section C

variable {V : Type} [CommGroup V] [Finite V]

namespace B510Fa

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Fa G G₁ G₂)

include h in
theorem exists_u_of_c
    (hV : ∀ v : V, v ^ 2 = 1) (hidx : (commV G₁ ⊔ fixV G₁).index = 2)
    (hiso : Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))))
    (hcard : Nat.card ↥(fixV G₁) = 2 ^ 4 * Nat.card ↥(fixV G))
    (hindec : ¬ ∃ A B : Subgroup V, fixV G < A ∧ fixV G < B ∧ XMod.IsInv ↥G₂ A ∧ XMod.IsInv ↥G₂ B ∧
      A ⊔ B = fixV G₁ ∧ A ⊓ B = fixV G)
    (hnatM : BinaryNaturalSL G₂ (modComm G₂ (fixV G₁) ⊔ fixV G) (fixV G) 3 1) :
    ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ ∧ ∀ g ∈ G₂, g u * u⁻¹ ∈ fixV G := by
  obtain ⟨u₀, hu₀⟩ : ∃ u : V, u ∉ commV G₁ ⊔ fixV G₁ := by
    by_contra hcon
    push Not at hcon
    have : commV G₁ ⊔ fixV G₁ = ⊤ := eq_top_iff.2 fun x _ => hcon x
    rw [← Subgroup.index_eq_one] at this
    omega
  set Y := fixV G₁ with hY
  set C := fixV G with hC
  set M : Subgroup V := modComm G₂ Y ⊔ C with hM
  have hM' : M = commSub Y G₂ ⊔ C := by rw [hM, modComm_eq_commSub]
  have hperf : ⁅G₂, G₂⁆ = G₂ := perfect_of_equiv_sl3 hiso.some
  have hCY : C ≤ Y := B1.fixV_le_fixV h.G₁_le
  have hCfix : ∀ g ∈ G₂, ∀ c ∈ C, g c = c := fun g hg c hc => hc g (h.G₂_le hg)
  have hcomm : commV G₂ ≤ commSub Y G₂ := commV_le_commSub_of_perfect hperf h.hc₂
  have hcM : ∀ g ∈ G₂, ∀ v : V, g v * v⁻¹ ∈ M := fun g hg v => by
    rw [hM']
    exact Subgroup.mem_sup_left (hcomm (Subgroup.subset_closure ⟨g, hg, v, rfl⟩))
  have hMY : M ≤ Y := by
    rw [hM']
    exact sup_le (commSub_le_of_invariant h.hLW₂) hCY
  have hCM : C ≤ M := le_sup_right
  obtain ⟨D⟩ := exists_natQuot3 hnatM
  have hLWM : ∀ g ∈ G₂, ∀ w ∈ M, g w ∈ M := by
    intro g hg w hw
    obtain ⟨γ, hγ⟩ := D.surj ⟨g, hg⟩
    have := D.inv γ w hw
    rw [hγ] at this
    exact this
  have hcardM : Nat.card ↥M = 8 * Nat.card ↥C := by rw [D.card_eq hCM]; norm_num
  have hcard' : Nat.card ↥Y = 16 * Nat.card ↥C := by rw [hcard]; norm_num
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hMlt : M < Y := lt_of_le_of_ne hMY fun heq => by
    rw [heq] at hcardM
    omega
  obtain ⟨y₀, hy₀Y, hy₀M⟩ := IsConcreteLE.exists_of_lt hMlt
  have hθs := D.thetaA_surj
  have hθa := D.thetaA_equiv hLWM
  have hker := D.thetaA_ker
  have hF : ∀ v : V, (fun γ => D.thetaA (cocyF hcM v (D.ρ γ))) ∈ Z1A (muF2 3) := by
    intro v γ δ
    have hzZ := cocyF_mem_Z1A hLWM hcM v
    show D.thetaA (cocyF hcM v (D.ρ (γ * δ))) = D.thetaA (cocyF hcM v (D.ρ γ)) +
      muF2 3 γ (D.thetaA (cocyF hcM v (D.ρ δ)))
    rw [map_mul, hzZ, map_add, hθa]
  have hvan : ∀ v : V, (fun γ => D.thetaA (cocyF hcM v (D.ρ γ))) ∈ B1A (muF2 3) →
      ∃ m : Additive ↥M, ∀ g : ↥G₂, (g : MulAut V) (v * (((Additive.toMul m : ↥M) : V))⁻¹) *
        (v * (((Additive.toMul m : ↥M) : V))⁻¹)⁻¹ ∈ C := by
    intro v hv
    obtain ⟨m, hm⟩ := coboundary_mod_of_image hLWM D.ρ D.surj (muF2 3) D.thetaA hθs hθa hv
    exact ⟨m, fun g => by
      rw [← cocyF_sub_coboundary hLWM hcM v m g]
      exact hker _ (hm g)⟩
  have hdiv : ∀ v v' : V, (fun γ => D.thetaA (cocyF hcM (v * v'⁻¹) (D.ρ γ))) =
      (fun γ => D.thetaA (cocyF hcM v (D.ρ γ))) - (fun γ => D.thetaA (cocyF hcM v' (D.ρ γ))) := by
    intro v v'
    funext γ
    rw [cocyF_div, Pi.sub_apply, map_sub]
    rfl
  have hy₀ : (fun γ => D.thetaA (cocyF hcM y₀ (D.ρ γ))) ∉ B1A (muF2 3) := by
    intro hB
    obtain ⟨m, hm⟩ := hvan y₀ hB
    set y₁ : V := y₀ * (((Additive.toMul m : ↥M) : V))⁻¹ with hy₁
    have hmM : ((Additive.toMul m : ↥M) : V) ∈ M := (Additive.toMul m : ↥M).2
    have hy₁Y : y₁ ∈ Y := Y.mul_mem hy₀Y (Y.inv_mem (hMY hmM))
    have hy₁M : y₁ ∉ M := by
      intro hmem
      apply hy₀M
      have : y₀ = y₁ * ((Additive.toMul m : ↥M) : V) := by rw [hy₁]; simp
      rw [this]
      exact M.mul_mem hmem hmM
    have hy₁C : ∀ g ∈ G₂, g y₁ * y₁⁻¹ ∈ C := fun g hg => hm ⟨g, hg⟩
    have hy₁sq : y₁ ^ 2 = 1 := hV y₁
    set B : Subgroup V := Subgroup.zpowers y₁ ⊔ C with hB'
    have hy₁B : y₁ ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁)
    have hBinv : ∀ g ∈ G₂, ∀ x ∈ B, g x ∈ B := by
      intro g hg x hx
      obtain ⟨y, hy, c, hcC, rfl⟩ := Subgroup.mem_sup.1 hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [map_mul, map_zpow, hCfix g hg c hcC]
      have hgy : g y₁ ∈ B := by
        have e : g y₁ = (g y₁ * y₁⁻¹) * y₁ := by simp
        rw [e]
        exact B.mul_mem (Subgroup.mem_sup_right (hy₁C g hg)) hy₁B
      exact B.mul_mem (B.zpow_mem hgy k) (Subgroup.mem_sup_right hcC)
    apply hindec
    refine ⟨M, B, ?_, ?_, fun a l hl => hLWM a a.2 l hl, fun a l hl => hBinv a a.2 l hl, ?_, ?_⟩
    · refine lt_of_le_of_ne hCM fun heq => ?_
      rw [← heq] at hcardM
      omega
    · refine lt_of_le_of_ne le_sup_right fun heq => ?_
      apply hy₁M
      have : y₁ ∈ C := by rw [heq]; exact hy₁B
      exact hCM this
    ·
      refine le_antisymm (sup_le hMY (sup_le (by
        rw [Subgroup.zpowers_le]; exact hy₁Y) hCY)) ?_
      have hidx2 : (M.subgroupOf Y).index = 2 := by
        have h1 := Subgroup.card_mul_index (M.subgroupOf Y)
        have h2 : Nat.card ↥(M.subgroupOf Y) = Nat.card ↥M :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv
        rw [h2, hcardM, hcard'] at h1
        have h3 : 8 * Nat.card ↥C * (M.subgroupOf Y).index = 8 * Nat.card ↥C * 2 := by
          rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_left (by omega) h3
      intro x hx
      have hxtop : (⟨x, hx⟩ : ↥Y) ∈ (M.subgroupOf Y) ⊔ Subgroup.zpowers (⟨y₁, hy₁Y⟩ : ↥Y) := by
        rw [sup_zpowers_eq_top (V := ↥Y) hidx2 (fun hmem => hy₁M hmem)]
        trivial
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hxtop
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      have hxeq : x = (a : V) * y₁ ^ k := by
        have := congrArg Subtype.val hab
        simpa using this.symm
      rw [hxeq]
      exact (M ⊔ B).mul_mem (Subgroup.mem_sup_left ha)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers y₁ k)))
    · refine le_antisymm ?_ (le_inf hCM le_sup_right)
      rintro x ⟨hxM, hxB⟩
      obtain ⟨y, hy, c, hcC, rfl⟩ := Subgroup.mem_sup.1 hxB
      rcases mem_zpowers_of_sq hy₁sq hy with h1 | h1
      · rw [h1, one_mul]
        exact hcC
      · exfalso
        apply hy₁M
        rw [h1] at hxM
        have := M.mul_mem hxM (M.inv_mem (hCM hcC))
        simpa using this
  rcases Z1A_three_cases (hF u₀) with h1 | h1
  · obtain ⟨m, hm⟩ := hvan u₀ h1
    refine ⟨u₀ * (((Additive.toMul m : ↥M) : V))⁻¹, ?_, fun g hg => hm ⟨g, hg⟩⟩
    intro hmem
    apply hu₀
    have hmM : ((Additive.toMul m : ↥M) : V) ∈ Y := hMY (Additive.toMul m : ↥M).2
    have e : u₀ = (u₀ * (((Additive.toMul m : ↥M) : V))⁻¹) * ((Additive.toMul m : ↥M) : V) := by simp
    rw [e]
    exact (commV G₁ ⊔ Y).mul_mem hmem (Subgroup.mem_sup_right hmM)
  · rcases Z1A_three_cases (hF y₀) with h2 | h2
    · exact absurd h2 hy₀
    · have h3 : (fun γ => D.thetaA (cocyF hcM (u₀ * y₀⁻¹) (D.ρ γ))) ∈ B1A (muF2 3) := by
        rw [hdiv]
        have := sub_mem h1 h2
        rwa [sub_sub_sub_cancel_right] at this
      obtain ⟨m, hm⟩ := hvan (u₀ * y₀⁻¹) h3
      refine ⟨u₀ * y₀⁻¹ * (((Additive.toMul m : ↥M) : V))⁻¹, ?_, fun g hg => hm ⟨g, hg⟩⟩
      intro hmem
      apply hu₀
      have hmM : ((Additive.toMul m : ↥M) : V) ∈ Y := hMY (Additive.toMul m : ↥M).2
      have e : u₀ = (u₀ * y₀⁻¹ * (((Additive.toMul m : ↥M) : V))⁻¹) *
          (((Additive.toMul m : ↥M) : V) * y₀) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      rw [e]
      exact (commV G₁ ⊔ Y).mul_mem hmem (Subgroup.mem_sup_right (Y.mul_mem hmM hy₀Y))

end B510Fa

end C

end FFC

end CFSG.Quasithin
