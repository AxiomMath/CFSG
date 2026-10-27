module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.Quasithin.AppendixH.H9.H92.RadCard.ElemAbelianMap

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Quasithin.H

theorem forall_linear_of_mem_aSet {K : Type} [Field K] [Finite K] {κ : Type}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n)
    {X A : Subgroup (MulAut (StdMod κ K))} {k : ℕ} (hk : 2 ≤ k) (hA : A ∈ aSet k X)
    (hsemi : ∀ a ∈ A, ∃ σ : K ≃+* K, IsSemilinear a σ) :
    ∀ a ∈ A, IsSemilinear a (RingEquiv.refl K) := by
  classical
  obtain ⟨τ, -, -, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (p := 2) (n := n) Nat.prime_two hn hK
  have hcycK : IsCyclic (K ≃+* K) :=
    ⟨τ, fun x => Subgroup.mem_zpowers_iff.mp (by rw [hgen]; exact Subgroup.mem_top x)⟩
  let σfun : ↥A → K ≃+* K :=
    fun a => Classical.choose (hsemi (a : MulAut (StdMod κ K)) a.2)
  let σ : ↥A →* (K ≃+* K) :=
    { toFun := σfun
      map_one' := by
        refine IsSemilinear.unique
          (Classical.choose_spec (hsemi (1 : ↥A) (Subgroup.one_mem A))) ?_
        exact isSemilinear_one
      map_mul' := by
        intro a b
        have ha := Classical.choose_spec (hsemi (a : MulAut (StdMod κ K)) a.2)
        have hb := Classical.choose_spec (hsemi (b : MulAut (StdMod κ K)) b.2)
        have hab := Classical.choose_spec
          (hsemi ((a * b : ↥A) : MulAut (StdMod κ K)) (a * b).2)
        have hmul : IsSemilinear ((a * b : ↥A) : MulAut (StdMod κ K))
            ((σfun b).trans (σfun a)) := by
          simpa only [Subgroup.coe_mul] using ha.mul hb
        have heq := IsSemilinear.unique hab hmul
        change σfun (a * b) = σfun a * σfun b
        exact heq }
  have hsq : ∀ a : ↥A, a * a = 1 := by
    intro a
    apply Subtype.ext
    simpa [pow_two] using hA.2.2.1.2 (a : MulAut (StdMod κ K)) a.2
  have hrange2 : Nat.card (σ.range) ≤ 2 := by
    have hcycTop : IsCyclic ↥(⊤ : Subgroup (K ≃+* K)) :=
      (MulEquiv.isCyclic (Subgroup.topEquiv (G := K ≃+* K))).mpr hcycK
    have hcycB : IsCyclic ↥(σ.range) :=
      @Subgroup.isCyclic_of_le (K ≃+* K) _ (σ.range) ⊤ le_top hcycTop
    have hsqrange : ∀ b ∈ σ.range, b * b = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul, hsq a, map_one]
    obtain ⟨g, hg⟩ := @IsCyclic.exists_generator ↥(σ.range) _ hcycB
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    refine Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one ?_)
    rw [pow_two]
    exact Subtype.ext (hsqrange (g : K ≃+* K) g.2)
  let A₀ : Subgroup (MulAut (StdMod κ K)) := σ.ker.map A.subtype
  have hA₀le : A₀ ≤ A := Subgroup.map_subtype_le σ.ker
  have hidx : (σ.ker).index ≤ 2 := by
    rw [Subgroup.index_ker]
    exact hrange2
  have hmq : mQuot A A₀ ≤ 1 := by
    have hrel : A₀.relIndex A = (σ.ker).index := by
      have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype)
        σ.ker (⊤ : Subgroup ↥A) A.subtype_injective
      rwa [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
    unfold mQuot
    rw [hrel]
    have hpos : 0 < (σ.ker).index := Nat.pos_of_ne_zero
      (Subgroup.index_ne_zero_of_finite (H := σ.ker))
    rcases (by omega : (σ.ker).index = 1 ∨ (σ.ker).index = 2) with h | h
    · rw [h]; simp
    · rw [h]
      change padicValNat 2 (2 ^ 1) ≤ 1
      rw [padicValNat.prime_pow]
  have hfixA : fixV A₀ = fixV A := hA.2.2.2 A₀ hA₀le (by omega)
  have hlinA₀ : ∀ a ∈ A₀, IsSemilinear a (RingEquiv.refl K) := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp ha
    have hb1 : σfun b = 1 := by simpa [σ] using hb
    have hs : IsSemilinear (b : MulAut (StdMod κ K)) (σfun b) :=
      Classical.choose_spec (hsemi (b : MulAut (StdMod κ K)) b.2)
    rw [hb1] at hs
    exact hs
  let hFK : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    @charP_of_card_eq_prime_pow K _ _ hFK 2 n (Fact.mk Nat.prime_two)
      (by
        show @Fintype.card K hFK = 2 ^ n
        rw [@Fintype.card_eq_nat_card K hFK]
        exact hK)
  have hW2 : ∀ w : StdMod κ K, w ^ 2 = 1 := by
    intro w
    apply Multiplicative.toAdd.injective
    rw [pow_two, toAdd_mul]
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    calc Multiplicative.toAdd w + Multiplicative.toAdd w
        = (2 : K) • Multiplicative.toAdd w := by rw [two_smul]
      _ = 0 := by rw [h2, zero_smul]
      _ = Multiplicative.toAdd (1 : StdMod κ K) := rfl
  have htop : (⊤ : Subgroup (StdMod κ K)) ≠ ⊥ := by
    let i : κ := Classical.choice ‹Nonempty κ›
    have hcardK : 1 < Nat.card K := by
      rw [hK]
      exact Nat.one_lt_pow (by omega) (by norm_num)
    have hcardF : 1 < @Fintype.card K hFK := by
      rw [@Fintype.card_eq_nat_card K hFK]
      exact hcardK
    obtain ⟨a, ha⟩ := @Fintype.exists_ne_of_one_lt_card K hFK hcardF (0 : K)
    let w0 : StdMod κ K := Multiplicative.ofAdd (Pi.single (M := fun _ => K) i a)
    have hw0 : w0 ≠ 1 := by
      intro h
      have hzero : Pi.single (M := fun _ => K) i a = 0 := by
        have := congrArg Multiplicative.toAdd h
        simpa [w0] using this
      have hval := congrFun hzero i
      exact ha (by simpa using hval)
    intro hbot
    have hmem : w0 ∈ (⊥ : Subgroup (StdMod κ K)) := by rw [← hbot]; trivial
    exact hw0 (Subgroup.mem_bot.mp hmem)
  obtain ⟨w, -, hw1, hwfix⟩ :=
    CFSG.Quasithin.B1.exists_fixed_ne_one hW2
      (isPGroup_of_isElemAbelian2 hA.2.2.1) (M := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _) htop
  have hw0 : Multiplicative.toAdd w ≠ 0 := by
    intro h0
    apply hw1
    apply Multiplicative.toAdd.injective
    simpa using h0
  have hne : ∃ i, Multiplicative.toAdd w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw0 (funext h)
  obtain ⟨i, hi⟩ := hne
  have hsub : ∀ c : K, Multiplicative.ofAdd (c • Multiplicative.toAdd w) ∈ fixV A := by
    intro c
    rw [← hfixA]
    rw [mem_fixV]
    intro a ha
    have halin := hlinA₀ a ha
    have haw : toAddMap a (Multiplicative.toAdd w) = Multiplicative.toAdd w :=
      congrArg Multiplicative.toAdd (hwfix a (hA₀le ha))
    have hsem := halin c (Multiplicative.toAdd w)
    change toAddMap a (c • Multiplicative.toAdd w) =
      c • Multiplicative.toAdd w
    rw [hsem, haw]
    rfl
  intro a ha
  by_contra hlin
  have hσa : σ ⟨a, ha⟩ ≠ 1 := by
    intro h1
    apply hlin
    have hs : IsSemilinear a (σfun ⟨a, ha⟩) := Classical.choose_spec (hsemi a ha)
    have h1' : σfun ⟨a, ha⟩ = 1 := by simpa [σ] using h1
    rw [h1'] at hs
    exact hs
  have hsem : IsSemilinear a (σfun ⟨a, ha⟩) := Classical.choose_spec (hsemi a ha)
  have hconst : ∀ c : K, c • Multiplicative.toAdd w =
      σfun ⟨a, ha⟩ c • Multiplicative.toAdd w := by
    intro c
    have hfixc : a (Multiplicative.ofAdd (c • Multiplicative.toAdd w)) =
        Multiplicative.ofAdd (c • Multiplicative.toAdd w) :=
      (mem_fixV.mp (hsub c)) a ha
    have hsemc := hsem c (Multiplicative.toAdd w)
    have hfixc' : toAddMap a (c • Multiplicative.toAdd w) =
        c • Multiplicative.toAdd w := congrArg Multiplicative.toAdd hfixc
    have hsemw : toAddMap a (Multiplicative.toAdd w) = Multiplicative.toAdd w :=
      congrArg Multiplicative.toAdd (hwfix a ha)
    rw [hfixc', hsemw] at hsemc
    exact hsemc
  have hσeq : ∀ c : K, σfun ⟨a, ha⟩ c = c := by
    intro c
    have hpoint := congrFun (hconst c) i
    simp only [Pi.smul_apply] at hpoint
    exact (mul_right_cancel₀ hi hpoint).symm
  exact hσa (RingEquiv.ext hσeq)

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit in
theorem actOnSub_range_le_normalizer {W : Type} [CommGroup W]
    {X A : Subgroup (MulAut W)} {I : Subgroup W}
    (hXI : ∀ x ∈ X, ∀ u ∈ I, x u ∈ I)
    (hAI : ∀ a ∈ A, ∀ u ∈ I, a u ∈ I)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut W))) :
    (actOnSub hAI).range ≤
      Subgroup.normalizer ((actOnSub hXI).range : Set (MulAut ↥I)) := by
  intro g hg
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
  rw [Subgroup.mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.mp hf
    rw [← hxeq]
    refine ⟨⟨(a : MulAut W) * (x : MulAut W) * (a : MulAut W)⁻¹, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hAX a.2) (x : MulAut W)).mp x.2
    · rfl
  · intro hf
    obtain ⟨x, hxeq⟩ := MonoidHom.mem_range.mp hf
    refine ⟨⟨(a : MulAut W)⁻¹ * (x : MulAut W) * (a : MulAut W), ?_⟩, ?_⟩
    · simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (X : Set (MulAut W))).inv_mem (hAX a.2))
        (x : MulAut W)).mp x.2
    · have hf' : f = (actOnSub hAI a)⁻¹ * (actOnSub hXI x) * (actOnSub hAI a) := by
        rw [hxeq]
        group
      rw [hf']
      rfl

theorem mem_aSet_actOnSub {W : Type} [CommGroup W] [Finite W] {k : ℕ}
    {X A : Subgroup (MulAut W)} (hA : A ∈ aSet k X) {I : Subgroup W}
    (hI : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I) {Y : Subgroup (MulAut ↥I)}
    (hY : (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI).range ≤ Y)
    (hne : (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI).range ≠ ⊥) :
    (CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI).range ∈ aSet k Y := by
  classical
  let f := CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub hI
  let B : Subgroup (MulAut ↥I) := f.range
  change B ∈ aSet k Y
  have hcomm : ∀ a ∈ (⊤ : Subgroup ↥A), ∀ b ∈ (⊤ : Subgroup ↥A), a * b = b * a := by
    intro a _ b _
    apply Subtype.ext
    exact hA.2.2.1.1 (a : MulAut W) a.2 (b : MulAut W) b.2
  have hsq : ∀ a ∈ (⊤ : Subgroup ↥A), a * a = 1 := by
    intro a _
    apply Subtype.ext
    simpa [pow_two] using hA.2.2.1.2 (a : MulAut W) a.2
  refine ⟨hY, hne, ?_, ?_⟩
  · have hB : IsElemAbelian2 ((⊤ : Subgroup ↥A).map f) :=
      CFSG.ASVolI.ChH.isElemAbelian2_map_of_comm_sq f ⊤ hcomm hsq
    simpa [B, Subgroup.map_top] using hB
  · intro C hC hlt
    let D : Subgroup ↥A := C.comap f
    have hDmap : D.map f = C := Subgroup.map_comap_eq_self hC
    let Bpre : Subgroup (MulAut W) := D.map A.subtype
    have hBprele : Bpre ≤ A := Subgroup.map_subtype_le D
    have hmq : mQuot A Bpre = mQuot B C := by
      unfold mQuot
      have h1 : Bpre.relIndex A = D.relIndex ⊤ := by
        have h := Subgroup.relIndex_map_map_of_injective (f := A.subtype)
          D (⊤ : Subgroup ↥A) A.subtype_injective
        rwa [Subgroup.map_top, Subgroup.range_subtype] at h
      have h2 : C.relIndex B = D.relIndex ⊤ := by
        have h := Subgroup.relIndex_comap C f (⊤ : Subgroup ↥A)
        rw [Subgroup.map_top] at h
        exact h.symm
      rw [h1, h2]
    have hlt' : mQuot A Bpre < k := by rw [hmq]; exact hlt
    have hfix : fixV Bpre = fixV A := hA.2.2.2 Bpre hBprele hlt'
    have hCfix : ∀ w : ↥I, w ∈ fixV C ↔ (w : W) ∈ fixV Bpre := by
      intro w
      constructor
      · intro hw
        rw [mem_fixV] at hw ⊢
        intro b hb
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hb
        have hfd : f d ∈ C := hd
        have := congrArg Subtype.val (hw (f d) hfd)
        simpa [f, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
          using this
      · intro hw
        rw [mem_fixV] at hw ⊢
        intro c hc
        rw [← hDmap] at hc
        obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hc
        have hb : (d : MulAut W) ∈ Bpre := ⟨d, hd, rfl⟩
        have := hw (d : MulAut W) hb
        apply Subtype.ext
        simpa [f, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
          using this
    have hBfix : ∀ w : ↥I, w ∈ fixV B ↔ (w : W) ∈ fixV A := by
      intro w
      constructor
      · intro hw
        rw [mem_fixV] at hw ⊢
        intro a ha
        have hfa : f ⟨a, ha⟩ ∈ B := ⟨⟨a, ha⟩, rfl⟩
        have := congrArg Subtype.val (hw (f ⟨a, ha⟩) hfa)
        simpa [f, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
          using this
      · intro hw
        rw [mem_fixV] at hw ⊢
        intro b hb
        obtain ⟨a, rfl⟩ := hb
        apply Subtype.ext
        simpa [f, CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.actOnSub_apply]
          using hw a a.2
    ext w
    calc
      w ∈ fixV C ↔ (w : W) ∈ fixV Bpre := hCfix w
      _ ↔ (w : W) ∈ fixV A := by rw [hfix]
      _ ↔ w ∈ fixV B := (hBfix w).symm

end E3

end CFSG.Quasithin
