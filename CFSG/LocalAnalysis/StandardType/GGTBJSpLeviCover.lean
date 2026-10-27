module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpLeviAut
public import CFSG.LocalAnalysis.StandardType.GGTBJSpAutomizer

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot TableBSymp SpCoord TypeBDatum Multiplicative

theorem ggTBJ_sp_full_automizer_eq {p m : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    [CharP K 2] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K m) = spTorusSp hζ f) :
    (ggAutomizer ⊤ (spTorusSp (m := m) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
      signedAut m p := by
  refine ggTBJ_sp_zero_block_automizer_eq hp hζo hζ (fun _ => 1)
    (fun _ _ _ _ _ => Subgroup.mem_top _) (fun _ _ => Subgroup.mem_top _) ?_ Finset.univ
    (fun i => by simp) κ hκ
  intro x hx j _
  have h1 : x = 1 := funext fun i => hx i rfl
  rw [h1, map_one, one_mul, mul_one]

theorem ggTBJ_sp_cover_block_automizers {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type}
    [Group L'] [Finite L']
    (ψ₀ : L' →* CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup K m))
    (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup K m) →*
        MulAut (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSpGroup K m)))) L' ψ₀ A)
    (y : MulAut L') (hy : y ∈ A) (hy1 : y ≠ 1) {J : Subgroup L'}
    (hJ : CFSG.Open.IsComponentOf J (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup y))
    (hcount : p ^ 2 * Nat.card ↥(A ⊓ ⨅ j : J, MulAction.stabilizer (MulAut L') (j : L')) ≤
      Nat.card ↥A) :
    ∃ κ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A,
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).map
        (MulAut.congr κ.symm).toMonoidHom = signedAut m p ∧
      ((∃ Z : Finset (Fin m), 2 ≤ Z.card ∧ Z.card < m ∧
          (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
            (MulAut.congr κ.symm).toMonoidHom = signedSupportedAut m p Z ∧
          ∀ f : Fin m → Multiplicative (ZMod p), (∀ i ∈ Z, f i = 1) →
            ∀ j ∈ J, (κ f : MulAut L') j = j) ∨
        (∃ (S : Finset (Fin m)) (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1),
          3 ≤ S.card ∧ (∀ i, s i = 1 ∨ s i = -1) ∧
          (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
            (MulAut.congr κ.symm).toMonoidHom = twistedPermAut m p S s hs ∧
          ∀ (f : Fin m → Multiplicative (ZMod p)) (a : ZMod p),
            (∀ i ∈ S, f i = ofAdd (s i * a)) → ∀ j ∈ J, (κ f : MulAut L') j = j)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      A ≤ (MulAut.conj : L' →* MulAut L').range := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, ν, Θ, J₀, hζo, hνinj, hνrange, hνtorus, hAmap, hJmap,
      hJ₀, hcount_core, hWeyl⟩ := ggTBJ_sp_inner_model hp hp2 hpq ψ₀ A hA y hy hJ hcount
  let f₀ : Fin m → Multiplicative (ZMod p) := Θ.symm ⟨y, hy⟩
  let t : Fin m → Kˣ := fun i => zmodPowHom hζ (f₀ i)
  have ht : ∃ i, t i ≠ 1 := by
    by_contra h
    have hti : ∀ i, t i = 1 := by simpa only [not_exists, not_not] using h
    have hf₀ : f₀ = 1 := by
      funext i
      apply ReflSp.zmodPowHom_injective hζ hζo
      simpa [t] using hti i
    have hyone : y = 1 := by
      have h := congrArg (fun f => (Θ f : MulAut L')) hf₀
      simpa [f₀] using h
    exact hy1 hyone
  have hK4 : 4 ≤ Nat.card K := by
    have h2 : 2 ≤ Nat.card K := by
      haveI : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have h3 : 3 ≤ p := by
      have h := hp.two_le
      omega
    have hpos : 0 < Nat.card K - 1 := by omega
    have hle := Nat.le_of_dvd hpos hpq
    omega
  have hJdiag : CFSG.Assembly.IsComponentOf J₀
      (Subgroup.centralizer ({diagSp K m t} : Set (CFSG.Assembly.LargeEvenSpGroup K m))) := by
    simpa only [ggTBJSpC_spTorusSp_eq_diagSp, t, f₀] using hJ₀
  obtain ⟨lam, hperm, hmixed, hswap, hcentral, hIzero, hIpaired⟩ :=
    ggTBJ_sp_blockData_with_card hp hK4 hζ t hJdiag hcount_core
  let T := (spTorusSp (m := m) hζ).range
  let κ₀ : (Fin m → Multiplicative (ZMod p)) ≃* T :=
    MonoidHom.ofInjective (TableBSymp.spTorusSp_injective (m := m) hζ hζo)
  have hκ₀ : ∀ f, (κ₀ f : CFSG.Assembly.LargeEvenSpGroup K m) = spTorusSp hζ f := fun _ => rfl
  let eTA : T ≃* A := (T.equivMapOfInjective ν hνinj).trans (MulEquiv.subgroupCongr hAmap)
  let κ : (Fin m → Multiplicative (ZMod p)) ≃* A := κ₀.trans eTA
  have hκν : ∀ f, (κ f : MulAut L') = ν (spTorusSp hζ f) := fun _ => rfl
  have hcoords (Q : Subgroup (CFSG.Assembly.LargeEvenSpGroup K m)) :
      (ggAutomizer (Q.map ν) A).map (MulAut.congr κ.symm).toMonoidHom =
        (ggAutomizer Q T).map (MulAut.congr κ₀.symm).toMonoidHom := by
    rw [F4AutWeyl.ggAutomizer_map_eq hνinj Q T hAmap, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro u
    apply MulEquiv.ext
    intro f
    change κ₀.symm (eTA.symm (eTA (u (eTA.symm (eTA (κ₀ f)))))) = κ₀.symm (u (κ₀ f))
    rw [eTA.symm_apply_apply, eTA.symm_apply_apply]
  have hfull : (ggAutomizer (MulAut.conj : L' →* MulAut L').range A).map
      (MulAut.congr κ.symm).toMonoidHom = signedAut m p := by
    calc _ = (ggAutomizer ⊤ T).map (MulAut.congr κ₀.symm).toMonoidHom := by
          simpa only [Subgroup.map_top, hνrange] using hcoords ⊤
      _ = _ := ggTBJ_sp_full_automizer_eq hp hζo hζ κ₀ hκ₀
  have hcomp : (ggAutomizer (J.map (MulAut.conj : L' →* MulAut L')) A).map
      (MulAut.congr κ.symm).toMonoidHom =
        (ggAutomizer J₀ T).map (MulAut.congr κ₀.symm).toMonoidHom := by
    simpa only [hJmap] using hcoords J₀
  have hJperf : ⁅J, J⁆ = J := by
    rw [← Subgroup.map_subtype_commutator, hJ.2.2.1, Subgroup.map_top, Subgroup.range_subtype]
  have hfixJ : ∀ f, (∀ j₀ ∈ J₀, spTorusSp hζ f * j₀ = j₀ * spTorusSp hζ f) →
      ∀ j ∈ J, (κ f : MulAut L') j = j := by
    intro f hf
    refine USixTwo.fix_of_perfect (π := (MulAut.conj : L' →* MulAut L')) ?_ hJperf ?_
    · intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut L' => φ g) (MonoidHom.mem_ker.mp hz)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * z = z * g * z⁻¹ * z := by rw [h]
        _ = z * g := by group
    · intro j hj
      rw [MonoidHom.mem_ker]
      have hjJ₀ : MulAut.conj j ∈ J₀.map ν := by
        rw [hJmap]
        exact Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
      obtain ⟨j₀, hj₀, hνj₀⟩ := Subgroup.mem_map.mp hjJ₀
      have hc : (κ f : MulAut L') * MulAut.conj j = MulAut.conj j * (κ f : MulAut L') := by
        rw [hκν, ← hνj₀, ← map_mul, ← map_mul, hf j₀ hj₀]
      have hconj : (κ f : MulAut L') * MulAut.conj j * (κ f : MulAut L')⁻¹ =
          MulAut.conj ((κ f : MulAut L') j) := by
        refine MulEquiv.ext fun g => ?_
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul,
          map_mul, map_inv, MulAut.apply_inv_self]
      rw [map_mul, map_inv, ← hconj, hc, mul_inv_cancel_right, mul_inv_cancel]
  have hAinn : A ≤ (MulAut.conj : L' →* MulAut L').range := by
    rw [← hνrange, ← hAmap]
    exact Subgroup.map_le_range ν T
  refine ⟨κ, hfull, ?_, hWeyl, hAinn⟩
  by_cases hlam : lam = 1
  ·
    subst hlam
    let Z : Finset (Fin m) := Finset.univ.filter fun i => t i = 1
    have hZ : ∀ i, i ∈ Z ↔ t i = 1 := fun i => by simp [Z]
    have hZcard : 2 ≤ Z.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, Z] using hIzero rfl
    have hZlt : Z.card < m := by
      obtain ⟨i, hi⟩ := ht
      have hiZ : i ∉ Z := fun h => hi ((hZ i).mp h)
      have hlt : Z.card < (Finset.univ : Finset (Fin m)).card :=
        Finset.card_lt_card ⟨Finset.subset_univ Z, fun h => hiZ (h (Finset.mem_univ i))⟩
      simpa using hlt
    refine Or.inl ⟨Z, hZcard, hZlt, ?_, ?_⟩
    · rw [hcomp]
      exact ggTBJ_sp_zero_block_automizer_eq hp hζo hζ t
        (fun i k hik hi hk => hperm i k hik (hi.trans hk.symm) (Or.inl hi))
        (fun i hi => hswap rfl i hi)
        (fun x hx => hcentral x (Or.inl ⟨rfl, hx⟩)) Z hZ κ₀ hκ₀
    · intro f hf
      apply hfixJ f
      intro j₀ hj₀
      have hx : ∀ i, t i = 1 → zmodPowHom hζ (f i) = 1 := by
        intro i hi
        rw [hf i ((hZ i).mpr hi), map_one]
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ f] using
        hcentral (fun i => zmodPowHom hζ (f i)) (Or.inl ⟨rfl, hx⟩) j₀ hj₀
  ·
    let S : Finset (Fin m) := Finset.univ.filter fun i => t i = lam ∨ t i = lam⁻¹
    have hS : ∀ i, i ∈ S ↔ (t i = lam ∨ t i = lam⁻¹) := fun i => by simp [S]
    have hScard : 3 ≤ S.card := by
      have h := hIpaired hlam
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      simpa [S] using h
    let s : Fin m → ZMod p := fun i => if t i = lam⁻¹ then -1 else 1
    have hsgn : ∀ i, s i = 1 ∨ s i = -1 := by
      intro i
      by_cases hi : t i = lam⁻¹
      · exact Or.inr (by simp [s, hi])
      · exact Or.inl (by simp [s, hi])
    have hs : ∀ i, s i * s i = 1 := fun i => coord_sign_mul_self (hsgn i)
    have hspos : ∀ i, t i ≠ lam⁻¹ → s i = 1 := fun i hi => by simp [s, hi]
    have hsneg : ∀ i, t i = lam⁻¹ → s i = -1 := fun i hi => by simp [s, hi]
    refine Or.inr ⟨S, s, hs, hScard, hsgn, ?_, ?_⟩
    · rw [hcomp]
      exact ggTBJ_sp_class_block_automizer_eq hp hp2 hζo hζ t hlam hperm hmixed
        (fun x hx => hcentral x (Or.inr ⟨hlam, hx⟩)) s hs hspos hsneg S hS κ₀ hκ₀
    · intro f a hf
      apply hfixJ f
      intro j₀ hj₀
      have hx : ∃ c : Kˣ, ∀ i, (t i = lam → zmodPowHom hζ (f i) = c) ∧
          (t i = lam⁻¹ → zmodPowHom hζ (f i) = c⁻¹) := by
        have hlamInv : lam ≠ lam⁻¹ := by
          intro h
          have hsq : lam * lam = 1 :=
            (congrArg (fun z : Kˣ => z * lam) h).trans (inv_mul_cancel lam)
          have hsq' : (lam : K) ^ 2 = 1 := by
            simpa [pow_two] using congrArg (fun z : Kˣ => (z : K)) hsq
          have hzero : ((lam : K) - 1) * ((lam : K) - 1) = 0 := by
            have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
            linear_combination hsq' - ((lam : K) - 1) * htwo
          exact hlam (Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp hzero).elim id id)))
        refine ⟨zmodPowHom hζ (ofAdd a), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
        · rw [hf i ((hS i).mpr (Or.inl hi)), hspos i (by rw [hi]; exact hlamInv), one_mul]
        · rw [hf i ((hS i).mpr (Or.inr hi)), hsneg i hi, neg_one_mul, ofAdd_neg, map_inv]
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ f] using
        hcentral (fun i => zmodPowHom hζ (f i)) (Or.inr ⟨hlam, hx⟩) j₀ hj₀

end CFSG.StandardType

end
