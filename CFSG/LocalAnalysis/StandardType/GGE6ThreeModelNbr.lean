module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHeart
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three

section Nbr

variable {L' : Type} [Group L'] [Finite L'] {Z : Subgroup L'} {A : Subgroup (MulAut L')}
  {Φ : A →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup L'} {w : Fin 6 → L'}

theorem GGE6ThreeData.exists_ne_one_forall_comm (h : GGE6ThreeData Z A Φ T w)
    {Y : Subgroup (MulAut L')} (hYA : ∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hYp : ∀ f ∈ Y, ∃ k : ℕ, ∀ a ∈ A, f ^ 3 ^ k * a = a * f ^ 3 ^ k) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ f ∈ Y, f * a = a * f := by
  classical
  let ρ : Y →* MulAut A :=
    { toFun := fun f =>
        { toFun := fun a =>
            ⟨(f : MulAut L') * (a : MulAut L') * (f : MulAut L')⁻¹, hYA f f.2 a a.2⟩
          invFun := fun a =>
            ⟨(f : MulAut L')⁻¹ * (a : MulAut L') * (f : MulAut L'), by
              have hh := hYA f⁻¹ (f⁻¹).2 a a.2
              simpa only [inv_inv] using hh⟩
          left_inv := fun a => Subtype.ext (by
            show (f : MulAut L')⁻¹ * ((f : MulAut L') * (a : MulAut L') * (f : MulAut L')⁻¹) *
                (f : MulAut L') = (a : MulAut L')
            group)
          right_inv := fun a => Subtype.ext (by
            show (f : MulAut L') * ((f : MulAut L')⁻¹ * (a : MulAut L') * (f : MulAut L')) *
                (f : MulAut L')⁻¹ = (a : MulAut L')
            group)
          map_mul' := fun a b => Subtype.ext (by
            show (f : MulAut L') * ((a : MulAut L') * (b : MulAut L')) * (f : MulAut L')⁻¹ =
                ((f : MulAut L') * (a : MulAut L') * (f : MulAut L')⁻¹) *
                  ((f : MulAut L') * (b : MulAut L') * (f : MulAut L')⁻¹)
            group) }
      map_one' := by
        apply MulEquiv.ext
        intro a
        apply Subtype.ext
        show (1 : MulAut L') * (a : MulAut L') * (1 : MulAut L')⁻¹ = (a : MulAut L')
        simp
      map_mul' := by
        intro f g
        apply MulEquiv.ext
        intro a
        apply Subtype.ext
        show ((f * g : Y) : MulAut L') * (a : MulAut L') * ((f * g : Y) : MulAut L')⁻¹ =
            (f : MulAut L') * ((g : MulAut L') * (a : MulAut L') * (g : MulAut L')⁻¹) *
              (f : MulAut L')⁻¹
        rw [Subgroup.coe_mul]
        group }
  have hρ_apply : ∀ (f : Y) (a : A),
      ((ρ f) a : MulAut L') = (f : MulAut L') * (a : MulAut L') * (f : MulAut L')⁻¹ :=
    fun _ _ => rfl
  have hp : IsPGroup 3 ρ.range := by
    intro g
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp g.2
    obtain ⟨k, hk⟩ := hYp f f.2
    refine ⟨k, Subtype.ext ?_⟩
    show g.1 ^ 3 ^ k = 1
    rw [← hf, ← map_pow]
    apply MulEquiv.ext
    intro a
    show (ρ (f ^ 3 ^ k)) a = a
    apply Subtype.ext
    rw [hρ_apply (f ^ 3 ^ k) a]
    have hk' : (f : MulAut L') ^ 3 ^ k * (a : MulAut L') =
        (a : MulAut L') * (f : MulAut L') ^ 3 ^ k := hk a a.2
    change (f : MulAut L') ^ 3 ^ k * (a : MulAut L') *
        ((f : MulAut L') ^ 3 ^ k)⁻¹ = (a : MulAut L')
    rw [hk']
    group
  have hA3 : 3 ∣ Nat.card A := by
    rcases h.card_cases with ⟨hcard, _⟩ | ⟨hcard, _⟩
    · rw [hcard]; exact ⟨3 ^ 5, by norm_num⟩
    · rw [hcard]; exact ⟨3 ^ 4, by norm_num⟩
  have h1fix : (⟨1, A.one_mem⟩ : A) ∈ MulAction.fixedPoints ρ.range A := by
    rw [MulAction.mem_fixedPoints]
    intro g
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp g.2
    change (g.1 : MulAut A) (⟨1, A.one_mem⟩ : A) = ⟨1, A.one_mem⟩
    rw [← hf]
    apply Subtype.ext
    rw [hρ_apply f ⟨1, A.one_mem⟩]
    simp
  obtain ⟨b, hb, hne⟩ :=
    hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hA3 h1fix
  refine ⟨b.1, b.2, ?_, ?_⟩
  · intro hb1
    exact hne (Subtype.ext hb1.symm)
  · intro f hf
    let fY : Y := ⟨f, hf⟩
    have hfixb : (ρ fY) b = b := by
      have h1 := (MulAction.mem_fixedPoints.mp hb)
        (⟨ρ fY, MonoidHom.mem_range.mpr ⟨fY, rfl⟩⟩ : ρ.range)
      change (ρ fY) b = b at h1
      exact h1
    have hval : (fY : MulAut L') * (b : MulAut L') * (fY : MulAut L')⁻¹ = (b : MulAut L') := by
      have := congrArg Subtype.val hfixb
      rwa [hρ_apply fY b] at this
    simpa [fY] using (mul_inv_eq_iff_eq_mul).mp hval

theorem GGE6ThreeData.centralizes_heart (h : GGE6ThreeData Z A Φ T w)
    {Y : Subgroup (MulAut L')} (hYA : ∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hYp : ∀ f ∈ Y, ∃ k : ℕ, ∀ a ∈ A, f ^ 3 ^ k * a = a * f ^ 3 ^ k)
    (hYW : ∀ n ∈ (Subgroup.closure (Set.range w) : Set L'), ∀ f ∈ Y,
      MulAut.conj n * f * (MulAut.conj n)⁻¹ ∈ Y) :
    ∀ f ∈ Y, ∀ a ∈ heartOf Φ, f * a = a * f := by
  classical
  obtain ⟨a₀, ha₀A, ha₀ne, ha₀comm⟩ := h.exists_ne_one_forall_comm hYA hYp
  let F : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L'))
  have hFA : F ≤ A := inf_le_left
  have hFne : F ≠ ⊥ := by
    intro hbot
    have ha0F : a₀ ∈ F :=
      ⟨ha₀A, Subgroup.mem_centralizer_iff.mpr (fun y hy => ha₀comm y hy)⟩
    rw [hbot] at ha0F
    exact ha₀ne (Subgroup.mem_bot.mp ha0F)
  have hFinv : ∀ i, ∀ a ∈ F,
      MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹ ∈ F := by
    intro i a ha
    obtain ⟨haA, hacent⟩ := ha
    have hacent' : ∀ y ∈ Y, y * a = a * y := fun y hy =>
      Subgroup.mem_centralizer_iff.mp hacent y hy
    have hi : w i ∈ Subgroup.closure (Set.range w) := Subgroup.subset_closure ⟨i, rfl⟩
    refine ⟨h.closure_conj_mem hi a haA, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      have hy' : (MulAut.conj (w i))⁻¹ * y * MulAut.conj (w i) ∈ Y := by
        have h1 := hYW ((w i)⁻¹) (inv_mem hi) y hy
        simpa only [map_inv, inv_inv] using h1
      have hca : ((MulAut.conj (w i))⁻¹ * y * MulAut.conj (w i)) * a =
          a * ((MulAut.conj (w i))⁻¹ * y * MulAut.conj (w i)) := hacent' _ hy'
      calc y * (MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹)
          = MulAut.conj (w i) *
              (((MulAut.conj (w i))⁻¹ * y * MulAut.conj (w i)) * a) *
                (MulAut.conj (w i))⁻¹ := by group
        _ = MulAut.conj (w i) *
              (a * ((MulAut.conj (w i))⁻¹ * y * MulAut.conj (w i))) *
                (MulAut.conj (w i))⁻¹ := by rw [hca]
        _ = (MulAut.conj (w i) * a * (MulAut.conj (w i))⁻¹) * y := by group)
  have hHF : heartOf Φ ≤ F := h.heart_le_of_invariant hFA hFne hFinv
  intro f hf a ha
  exact (Subgroup.mem_centralizer_iff.mp (hHF ha).2) f hf

theorem GGE6ThreeData.comm_of_comm_heart
    (h : GGE6ThreeData Z A Φ T w) {f : MulAut L'}
    (hfA : ∀ a ∈ A, f * a * f⁻¹ ∈ A)
    (hfp : ∃ k : ℕ, ∀ a ∈ A, f ^ 3 ^ k * a = a * f ^ 3 ^ k)
    (hfH : ∀ a ∈ heartOf Φ, f * a = a * f) : ∀ a ∈ A, f * a = a * f := by
  classical
  have hfN : f ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    mem_normalizer_of_conj_mem hfA
  obtain ⟨c, u, _hc_ne, hfull⟩ := h.full f hfN
  let vv : A → (Fin Tag.E6.rank → ZMod 3) := fun a => Multiplicative.toAdd (Φ a)
  have hfullvv : ∀ a b : A, (b : MulAut L') = f * a * f⁻¹ →
      vv b = c • adAct .E6 3 u (vv a) := fun a b hab => hfull a b hab
  let φ : (Fin Tag.E6.rank → ZMod 3) → (Fin Tag.E6.rank → ZMod 3) :=
    fun v => c • adAct .E6 3 u v
  have hφ_apply : ∀ v, φ v = c • adAct .E6 3 u v := fun _ => rfl
  have hφ_fix_hyp : ∀ v ∈ NoOffRest.hypE6, φ v = v := by
    intro v hv
    obtain ⟨a, ha⟩ := h.exists_eq_of_mem_hypE6 hv
    have haH : (a : MulAut L') ∈ heartOf Φ := by
      rw [mem_heartOf_iff]
      exact ⟨a.2, by
        show Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6
        rw [ha]
        exact hv⟩
    have hconj : f * (a : MulAut L') * f⁻¹ = (a : MulAut L') := by
      have hc := hfH (a : MulAut L') haH
      rw [hc]
      group
    have hvv : vv a = φ (vv a) := hfullvv a a hconj.symm
    have hva : vv a = v := by
      show Multiplicative.toAdd (Φ a) = v
      rw [ha]
      rfl
    rw [← hva]
    exact hvv.symm
  have key : ∀ m : ℕ, ∀ a : A,
      ∃ b : A, (b : MulAut L') = f ^ m * (a : MulAut L') * (f ^ m)⁻¹ ∧
        vv b = (φ^[m]) (vv a) := by
    intro m
    induction m with
    | zero =>
      intro a
      refine ⟨a, ?_, ?_⟩
      · simp
      · simp [Function.iterate_zero_apply]
    | succ m ih =>
      intro a
      obtain ⟨b, hb, hbΦ⟩ := ih a
      refine ⟨⟨f * (b : MulAut L') * f⁻¹, hfA (b : MulAut L') b.2⟩, ?_, ?_⟩
      · show f * (b : MulAut L') * f⁻¹ = f ^ (m + 1) * (a : MulAut L') * (f ^ (m + 1))⁻¹
        rw [hb, pow_succ']
        group
      · show vv ⟨f * (b : MulAut L') * f⁻¹, hfA (b : MulAut L') b.2⟩ =
            (φ^[m + 1]) (vv a)
        rw [hfullvv b ⟨f * (b : MulAut L') * f⁻¹, hfA (b : MulAut L') b.2⟩ rfl, hbΦ,
          Function.iterate_succ_apply']
  rcases h.card_cases with ⟨_hcard, honto⟩ | ⟨_hcard, hmem⟩
  ·
    obtain ⟨k, hk⟩ := hfp
    have hφ_iter_id : ∀ v, (φ^[3 ^ k]) v = v := by
      intro v
      obtain ⟨a, ha⟩ := honto v
      obtain ⟨b, hb, hbΦ⟩ := key (3 ^ k) a
      have hbeq : b = a := by
        apply Subtype.ext
        show (b : MulAut L') = (a : MulAut L')
        rw [hb, hk a a.2]
        group
      have hφa : (φ^[3 ^ k]) (vv a) = vv a := by
        rw [← hbΦ, hbeq]
      have hva : vv a = v := by
        show Multiplicative.toAdd (Φ a) = v
        rw [ha]
        rfl
      rw [← hva]
      exact hφa
    have hc1 : c = 1 := by
      obtain ⟨x₀, hx₀⟩ := exists_not_mem_hypE6
      have hx₀ne : NoOffRest.kDotP 3 x₀ ≠ 0 := fun h0 => hx₀ (NoOffRest.mem_hypE6.mpr h0)
      have hkdot : ∀ m : ℕ,
          NoOffRest.kDotP 3 ((φ^[m]) x₀) = c ^ m * NoOffRest.kDotP 3 x₀ := by
        intro m
        induction m with
        | zero => simp [Function.iterate_zero_apply]
        | succ m ih =>
          rw [Function.iterate_succ_apply', hφ_apply, NoOffRest.kDotP_smul,
            NoOffRest.kDot_adAct, ih]
          ring
      have hfixk : c ^ 3 ^ k * NoOffRest.kDotP 3 x₀ = NoOffRest.kDotP 3 x₀ := by
        rw [← hkdot (3 ^ k), hφ_iter_id x₀]
      rw [ZMod.pow_card_pow] at hfixk
      exact mul_right_cancel₀ hx₀ne (by rw [one_mul]; exact hfixk)
    have hu1 : u = 1 := by
      apply eq_one_of_adAct_eq_on_hypE6
      intro x hx
      have hx' : c • adAct .E6 3 u x = x := hφ_fix_hyp x hx
      rw [hc1, one_smul] at hx'
      exact hx'
    intro a ha
    let aA : A := ⟨a, ha⟩
    have hconj : f * (aA : MulAut L') * f⁻¹ = (aA : MulAut L') := by
      have hb := hfullvv aA ⟨f * (aA : MulAut L') * f⁻¹, hfA (aA : MulAut L') aA.2⟩ rfl
      rw [hc1, hu1, adAct_one, one_smul] at hb
      have hbT : Multiplicative.toAdd (Φ ⟨f * (aA : MulAut L') * f⁻¹,
            hfA (aA : MulAut L') aA.2⟩) = Multiplicative.toAdd (Φ aA) := hb
      have hb' : (⟨f * (aA : MulAut L') * f⁻¹, hfA (aA : MulAut L') aA.2⟩ : A) = aA :=
        h.injective (Multiplicative.toAdd.injective hbT)
      exact congrArg Subtype.val hb'
    simpa [aA] using (mul_inv_eq_iff_eq_mul).mp hconj
  ·
    intro a ha
    exact hfH a (by
      rw [mem_heartOf_iff]
      exact ⟨ha, hmem ⟨a, ha⟩⟩)

theorem GGE6ThreeData.nbrConcl
    (h : GGE6ThreeData Z A Φ T w) : U63TB.NbrConcl 3 Z A := by
  refine ⟨(Subgroup.closure (Set.range w) : Set L'), ?_, ?_⟩
  · intro n hn
    exact h.closure_weyl hn
  · intro Y _ _ hWY hYA hYp f hf a ha
    exact h.comm_of_comm_heart (f := f) (hYA f hf) (hYp f hf)
      (h.centralizes_heart hYA hYp hWY f hf) a ha

end Nbr

end CFSG.StandardType
