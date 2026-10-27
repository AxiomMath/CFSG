module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClElation
public import CFSG.RankThree.GF2n.Stroth80.Sec310Main
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

theorem card_sq_le_of_elationFull {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hdim : Module.finrank K V = 4) {e : V} (he : e ≠ 0)
    {A : Subgroup (V ≃ₗ[K] V)} (hful : Classify.ElationFull F (A : Set (V ≃ₗ[K] V)) e) :
    Nat.card K ^ 2 ≤ Nat.card A := by
  classical
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨f₀, hf₀⟩ : ∃ f₀, F e f₀ ≠ 0 := by
    by_contra hcon
    exact he (hnd.1 e fun y => by_contra fun hy => hcon ⟨y, hy⟩)
  obtain ⟨f, hef⟩ : ∃ f, F e f = 1 :=
    ⟨(F e f₀)⁻¹ • f₀, by rw [map_smul, smul_eq_mul]; exact inv_mul_cancel₀ hf₀⟩
  have hfe : F f e = 1 := by
    rw [← Classify.form_comm halt e f]
    exact hef
  have hee : F e e = 0 := Classify.form_self halt e
  have hff : F f f = 0 := Classify.form_self halt f
  have hli : LinearIndependent K ![e, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : F (s • e + t • f) f = 0 := by rw [hst]; simp
    have h2 : F (s • e + t • f) e = 0 := by rw [hst]; simp
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef,
      hee, hff, hfe, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    exact ⟨h1, h2⟩
  set W : Submodule K V := Submodule.span K (Set.range ![e, f]) with hW
  have hWe : e ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hWf : f ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hfinW : Module.finrank K W = 2 := by
    rw [hW, finrank_span_eq_card hli]
    simp
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have hfinS : Module.finrank K W.dualAnnihilator = 2 := by omega
  have hcardS : Nat.card W.dualAnnihilator = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := W.dualAnnihilator), hfinS]
  have hchoice : ∀ φ : W.dualAnnihilator,
      ∃ g ∈ A, ∀ v, F v e = 0 → g v = v + (φ : Module.Dual K V) v • e :=
    fun φ => hful φ ((Submodule.mem_dualAnnihilator _).mp φ.2 e hWe)
  choose g hgA hg using hchoice
  have hinj : Function.Injective fun φ : W.dualAnnihilator => (⟨g φ, hgA φ⟩ : A) := by
    intro φ ψ hφψ
    have hgeq : g φ = g ψ := congrArg Subtype.val hφψ
    have hU : ∀ v, F v e = 0 → (φ : Module.Dual K V) v = (ψ : Module.Dual K V) v := by
      intro v hv
      have h1 := hg φ v hv
      have h2 := hg ψ v hv
      rw [hgeq] at h1
      have h3 : ((φ : Module.Dual K V) v) • e = ((ψ : Module.Dual K V) v) • e :=
        add_left_cancel (h1.symm.trans h2)
      have h4 : ((φ : Module.Dual K V) v - (ψ : Module.Dual K V) v) • e = 0 := by
        rw [sub_smul, h3, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right he)
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    have hφf : (φ : Module.Dual K V) f = 0 := (Submodule.mem_dualAnnihilator _).mp φ.2 f hWf
    have hψf : (ψ : Module.Dual K V) f = 0 := (Submodule.mem_dualAnnihilator _).mp ψ.2 f hWf
    have hvU : F (v - F v e • f) e = 0 := by
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hfe,
        mul_one, sub_self]
    have hdec : v = (v - F v e • f) + F v e • f := by abel
    rw [hdec, map_add, map_add, hU _ hvU, map_smul, map_smul, hφf, hψf]
  calc Nat.card K ^ 2 = Nat.card W.dualAnnihilator := hcardS.symm
    _ ≤ Nat.card A := Nat.card_le_card_of_injective _ hinj

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth311RootOrder_of_34 (h34 : Stroth34Statement) : Stroth311RootOrderStatement := by
  classical
  intro G _ _ M Q Z B hc n hw hn hno hgen t ht htQ hR hnot hΩ
  have hs : Sec5Hyp hc n t := ⟨hw, hn, hno, hgen, ht, htQ⟩
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c _ he => hc.smul_mem_img_Vt h t c he
  obtain ⟨D⟩ := hc.exists_reprData h34 hs hnot h hS
  have hKZ : Nat.card (GaloisField 2 n') = Nat.card Z := h.card
  have hdim4 : Module.finrank (GaloisField 2 n') ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) = 4 := by
    obtain ⟨K₁, _, _, hK₁, φ₁, -, -, hsec⟩ := hΩ
    have hcardV := card_eq_of_sectionAct (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (t := t))
      hsec
    have hcardM := M₀.card_eq (hc.Vt_le_Q t) (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B)
      (t := t))
    have hfin : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
        Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => mem_imgSub.symm)
    have hpow : Nat.card ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) =
        Nat.card (GaloisField 2 n') ^ Module.finrank (GaloisField 2 n')
          ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS) :=
      Module.natCard_eq_pow_finrank (K := GaloisField 2 n')
        (V := ↥(imgSub M₀ (Vt M (LB M Q B) B Z t) hS))
    rw [hcardV, hfin] at hcardM
    have h2 := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcardM
    simp only [Fintype.card_sum, Fintype.card_fin] at h2
    rw [hK₁, hpow, hKZ] at h2
    have h3 : 2 ≤ Nat.card Z := by
      have := hc.hyp.q4
      omega
    have h4 := Nat.pow_right_injective h3 h2
    omega
  obtain ⟨e, he0, -, -, heful⟩ := D.elation_data h34 hs h (by omega) (m := 1) M.one_mem
    (by rw [conjSubgroup_one]; exact ht)
  rw [conjSubgroup_one] at heful
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hcount := card_sq_le_of_elationFull D.nondeg D.alt hdim4 he0 heful
  have hrel : Nat.card (((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map D.ρ) =
      (hc.CN t).relIndex (LB M Q B) := by
    rw [← Subgroup.relIndex_ker, D.ker, Subgroup.relIndex_subgroupOf hLR]
  rw [← hrel, ← hKZ]
  exact hcount

end CFSG.RankThree.GF2n.Stroth80
