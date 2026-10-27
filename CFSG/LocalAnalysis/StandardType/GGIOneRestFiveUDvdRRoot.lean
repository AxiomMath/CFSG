module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRZMod
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdRNode
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDvdEndNode
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdSwap
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Model
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitaryDvd

public section

namespace CFSG.StandardType.IOneUDvdR

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU CFSG.StandardType.SmallU
  CFSG.StandardType.TableBUE

@[expose] def GGIOneUnitaryDvdRootSixTwoInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ), Nat.card K = (2 ^ 1) ^ 2 → p.Prime →
    p ∣ 2 ^ 1 + 1 → p ∣ 6 →
      GGEndNodeRoot p (ggUnitaryTorusRank p 6) (UnitaryR K 1 6) (UnitaryI K 1 6)

@[expose] def fixSubgroup {L' : Type} [Group L'] (x : L') : Subgroup (MulAut L') where
  carrier := {h | h x = x}
  mul_mem' := fun {h k} hh hk => by
    change h x = x at hh
    change k x = x at hk
    change (h * k) x = x
    rw [MulAut.mul_apply, hk, hh]
  one_mem' := by
    change (1 : MulAut L') x = x
    rfl
  inv_mem' := fun {h} hh => by
    change h x = x at hh
    change h⁻¹ x = x
    calc h⁻¹ x = h⁻¹ (h x) := by rw [hh]
      _ = x := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem centEnd_of_node {n d : ℕ} {K : Type} [Field K] [Finite K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} (hM : UnitTB.Model φ) {A : Subgroup (MulAut L')}
    {g : MulAut L'} {σ : Fin d → Kˣ} (hg : ActsU φ g σ) {S : Finset (Fin d)}
    (hτ : TableBUE.IsNodeOn σ S) (hbig : BigOK n S)
    (hcent : ∀ a' ∈ A, (∀ y ∈ blockSU (K := K) (n := n) S, a' (φ y) = φ y) →
      a' ∈ Subgroup.zpowers g) :
    IsComponentOf (LargeEvenLayer (ggFix g)) (ggFix g) ∧
      LargeEvenLayer (ggFix g) = (blockSU (K := K) (n := n) S).map φ ∧ GGCentEnd A g := by
  obtain ⟨hlay, hcomp⟩ := layer_eq_block_of_isNodeOn hM hg hτ hbig
  have hfixS : ∀ i ∈ S, ∀ j ∈ S, σ i = σ j := hτ.1
  have hgfix : ∀ y ∈ blockSU (K := K) (n := n) S, g (φ y) = φ y := fun y hy =>
    ActsU.fix_of_const hg hfixS hy
  refine ⟨hcomp, hlay, fun a' ha' => ⟨fun hfix => hcent a' ha' fun y hy => hfix (φ y) ?_,
    fun hz => ?_⟩⟩
  · rw [hlay]
    exact ⟨y, hy, rfl⟩
  · rw [hlay]
    rintro _ ⟨y, hy, rfl⟩
    have hH : Subgroup.zpowers g ≤ fixSubgroup (φ y) :=
      Subgroup.zpowers_le.mpr (show g ∈ fixSubgroup (φ y) from hgfix y hy)
    exact hH hz

theorem not_largeEvenSmall_layer_of_node {n d : ℕ} {K : Type} [Field K] {L' : Type} [Group L']
    {φ : ↥(unitarySU 2 n K d) →* L'} {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)}
    (hM : UnitTB.Model φ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥) {S : Finset (Fin d)}
    (hSne : S ≠ Finset.univ) (hbigcard : 25920 < Nat.card (blockSU (K := K) (n := n) S)) :
    ¬ LargeEvenSmall ((blockSU (K := K) (n := n) S).map φ) :=
  not_largeEvenSmall_of_map_big ψ _
    (bigLayer_map_of_block (fun _ hx h1 => psi_phi_eq_one_of_block hM hker hZ hSne hx h1)
      hbigcard)

theorem endNode_of_model {n d p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hdn : (d, n) ≠ (6, 1))
    {L' : Type} [Group L'] [Finite L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    (hM : UnitTB.Model φ)
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K d)} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') {A : Subgroup (MulAut L')}
    (hA : CFSG.Open.IsElemAbelian p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hr : p ^ (d - 3) ≤ Nat.card A)
    {U : Subgroup (LargeEvenProj (unitarySU 2 n K d))} (hU1 : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hAU : ∀ a ∈ A, ∀ l : L', ψ l ∈ U → ψ (a l) ∈ U) :
    ∃ a : MulAut L', GGIsEndNode A a ∧ GGNonSmallRule p A a ∧
      ∃ U' : Subgroup L', U' ≤ LargeEvenLayer (ggFix a) ∧ U' ≠ ⊥ ∧ IsPGroup 2 U' ∧
        ∀ a' ∈ A, ∀ u ∈ U', a' u ∈ U' := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hd3 : 3 ≤ d := by omega
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have hZ : Subgroup.center (LargeEvenProj (unitarySU 2 n K d)) = ⊥ :=
    TableBUE.center_proj_eq_bot hK hd3 hdq
  have hAp : ∀ a ∈ A, a ^ p = 1 := fun a ha => hA.2 a ha
  obtain ⟨s, t, hst, hpair⟩ :=
    SmallU.exists_pair hM hK (by omega) hp hpq hψ hker hZ hAp hdiag hU1 hU2 hAU
  obtain ⟨ν, hν⟩ := SmallU.exists_nu_actsU hM hd3 hdiag s
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd hp (TableBUE.dvd_card_sub_one hK hpq)
  set F : Finset (Fin d) := ({s, t} : Finset (Fin d))ᶜ with hFdef
  have hs1 : ∀ g : ↥A, ν g s = 1 := fun g => (hν g).2
  have ht1 : ∀ g : ↥A, ν g t = 1 := fun g => by
    rw [← hpair g.1 g.2 (ν g) (hν g).1, (hν g).2]
  have hpow : ∀ (g : ↥A) (k : Fin d), ((ν g k : Kˣ) : K) ^ p = 1 := by
    intro g k
    have h := SmallU.ActsU.pow_ratio hM hd3 (hν g).1 (hAp g g.2) k s
    rw [(hν g).2, inv_one, mul_one] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hF : ∀ (g : ↥A) (k : Fin d), k ∉ F → ν g k = 1 := by
    intro g k hk
    simp only [hFdef, Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
      not_not] at hk
    rcases hk with h | h
    · rw [h]
      exact hs1 g
    · rw [h]
      exact ht1 g
  have hinj : Function.Injective ν := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply Subtype.ext
    have h1 := (hν g).1
    rw [hg] at h1
    exact SmallU.ActsU.eq_one_of_const hM h1 s (fun _ _ => rfl)
  obtain ⟨v, hvmul, hvzero, hvform, hvinj, hvpow, M, hM_mem, hrank⟩ :=
    exists_zmod_span hζ F ν hpow hF hinj (d - 3) hr
  have hFcard : Fintype.card ↥F = d - 2 := by
    rw [Fintype.card_coe, hFdef, Finset.card_compl, Fintype.card_fin, Finset.card_pair hst]
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have h3F : 2 < Fintype.card ↥F := by omega
  have hdim : Fintype.card ↥F - 1 ≤ Module.finrank (ZMod p) M := by omega
  have hnode : ∃ g : ↥A, ∃ T : Finset (Fin d), T.card ≤ 2 ∧ (∀ i, ν g i ≠ 1 → i ∈ T) ∧
      (∀ i j, ν g i ≠ 1 → ν g j = ν g i → j = i) ∧ (∃ i, ν g i ≠ 1) ∧
      (∀ y ∈ M, (∀ k : ↥F, ν g k.1 = 1 → y k = 0) → ∃ α : ZMod p, y = α • v g) := by
    rcases IOneUDvd.exists_endNode_of_finrank hp2 h3F hdim with
      ⟨c, hc⟩ | ⟨c, c', hcc', x, hxM, hx0, hxc, hxc', hxne, huniq⟩
    ·
      obtain ⟨g, hg⟩ := (hM_mem _).mp hc
      have hvne : ∀ k : ↥F, k ≠ c → v g k = 0 := fun k hk => by
        rw [hg, Pi.single_apply, if_neg hk]
      have hν1 : ∀ k : ↥F, k ≠ c → ν g k.1 = 1 := fun k hk => (hvzero g k).mp (hvne k hk)
      have hcne : ν g c.1 ≠ 1 := fun h => by
        have h1 := (hvzero g c).mpr h
        rw [hg, Pi.single_apply, if_pos rfl] at h1
        exact one_ne_zero h1
      have hTmem : ∀ i, ν g i ≠ 1 → i = c.1 := by
        intro i hi
        by_cases hiF : i ∈ F
        · have hk : (⟨i, hiF⟩ : ↥F) = c := by
            by_contra hne
            exact hi (hν1 ⟨i, hiF⟩ hne)
          exact congrArg Subtype.val hk
        · exact absurd (hF g i hiF) hi
      refine ⟨g, {c.1}, by simp, fun i hi => Finset.mem_singleton.mpr (hTmem i hi), ?_,
        ⟨c.1, hcne⟩, ?_⟩
      · intro i j hi hj
        rw [hTmem i hi, hTmem j (by rw [hj]; exact hi)]
      · intro y _ hy
        refine ⟨y c, ?_⟩
        rw [hg]
        funext k
        by_cases hkc : k = c
        · rw [hkc]
          simp
        · have hyk : y k = 0 := hy k (hν1 k hkc)
          simp [Pi.single_apply, hkc, hyk]
    ·
      obtain ⟨g, hg⟩ := (hM_mem _).mp hxM
      have hν1 : ∀ k : ↥F, k ≠ c → k ≠ c' → ν g k.1 = 1 := fun k hk1 hk2 =>
        (hvzero g k).mp (by rw [hg]; exact hx0 k hk1 hk2)
      have hdistν : ν g c.1 ≠ ν g c'.1 := by
        intro h
        apply hxne
        have h' : v g c = v g c' := by rw [hvform, hvform, h]
        rw [hg] at h'
        exact h'
      have hcne : ν g c.1 ≠ 1 := fun h => hxc (by
        rw [← hg]
        exact (hvzero g c).mpr h)
      have hTmem : ∀ i, ν g i ≠ 1 → i = c.1 ∨ i = c'.1 := by
        intro i hi
        by_cases hiF : i ∈ F
        · by_cases hk1 : (⟨i, hiF⟩ : ↥F) = c
          · exact Or.inl (congrArg Subtype.val hk1)
          · by_cases hk2 : (⟨i, hiF⟩ : ↥F) = c'
            · exact Or.inr (congrArg Subtype.val hk2)
            · exact absurd (hν1 ⟨i, hiF⟩ hk1 hk2) hi
        · exact absurd (hF g i hiF) hi
      refine ⟨g, {c.1, c'.1}, Finset.card_le_two, fun i hi => ?_, ?_, ⟨c.1, hcne⟩, ?_⟩
      · rcases hTmem i hi with h | h
        · rw [h]
          simp
        · rw [h]
          simp
      · intro i j hi hj
        have hj' : ν g j ≠ 1 := by
          rw [hj]
          exact hi
        rcases hTmem i hi with hi' | hi' <;> rcases hTmem j hj' with hj'' | hj''
        · rw [hi', hj'']
        · rw [hi', hj''] at hj
          exact absurd hj.symm hdistν
        · rw [hi', hj''] at hj
          exact absurd hj hdistν
        · rw [hi', hj'']
      · intro y hy hyk
        obtain ⟨α, hα⟩ := huniq y hy (fun k hk1 hk2 => hyk k (hν1 k hk1 hk2))
        exact ⟨α, by rw [hg]; exact hα⟩
  obtain ⟨g, T, hTcard, hT, hdist, ⟨c₀, hc₀⟩, hlin⟩ := hnode
  have hsS : s ∈ SmallU.cls (ν g) s := SmallU.mem_cls.mpr rfl
  have htS : t ∈ SmallU.cls (ν g) s := SmallU.mem_cls.mpr (by rw [ht1 g, hs1 g])
  have hτ : TableBUE.IsNodeOn (ν g) (SmallU.cls (ν g) s) := by
    unfold TableBUE.IsNodeOn
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [SmallU.mem_cls.mp hi, SmallU.mem_cls.mp hj]
    · intro hν'
      have hi1 : ν g i ≠ 1 := fun h1 => hi (SmallU.mem_cls.mpr (by rw [h1, hs1 g]))
      exact hj (hdist i j hi1 hν')
  have hScard : d - 2 ≤ (SmallU.cls (ν g) s).card := by
    have hsub : (SmallU.cls (ν g) s)ᶜ ⊆ T := fun i hi => hT i (fun h1 =>
      (Finset.mem_compl.mp hi) (SmallU.mem_cls.mpr (by rw [h1, hs1 g])))
    have h1 := Finset.card_le_card hsub
    have h2 : (SmallU.cls (ν g) s)ᶜ.card = d - (SmallU.cls (ν g) s).card := by
      rw [Finset.card_compl, Fintype.card_fin]
    omega
  have hd9 : n = 1 → 9 ≤ d := by
    intro hn1
    subst hn1
    have h3p : p ∣ 3 := by simpa using hpq
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3p
    subst hp3
    obtain ⟨k, hk⟩ := hpd
    have hd6 : d ≠ 6 := fun h => hdn (by rw [h])
    omega
  have hBig : BigOK n (SmallU.cls (ν g) s) := by
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · have h9 := hd9 (by omega)
      exact Or.inl (by omega)
    · exact Or.inr ⟨hn2, by omega⟩
  have hcent : ∀ a' ∈ A, (∀ y ∈ blockSU (K := K) (n := n) (SmallU.cls (ν g) s),
      a' (φ y) = φ y) → a' ∈ Subgroup.zpowers (g : MulAut L') := by
    intro a' ha' hfix
    have hk₀ : c₀ ∉ SmallU.cls (ν g) s := fun h => hc₀ ((SmallU.mem_cls.mp h).trans (hs1 g))
    have hconst := ActsU.const_of_fix hM (hν ⟨a', ha'⟩).1 hk₀ hfix
    have hyS : ∀ k : ↥F, ν g k.1 = 1 → ν ⟨a', ha'⟩ k.1 = 1 := fun k hk => by
      have hkS : k.1 ∈ SmallU.cls (ν g) s := SmallU.mem_cls.mpr (by rw [hk, hs1 g])
      exact (hconst k.1 hkS s hsS).trans (hs1 _)
    obtain ⟨α, hα⟩ := hlin (v ⟨a', ha'⟩) ((hM_mem _).mpr ⟨⟨a', ha'⟩, rfl⟩)
      (fun k hk => (hvzero _ k).mpr (hyS k hk))
    have hv2 : v ⟨a', ha'⟩ = v (g ^ α.val) := by
      rw [hvpow, ZMod.natCast_zmod_val]
      exact hα
    have hEq : (⟨a', ha'⟩ : ↥A) = g ^ α.val := hvinj hv2
    have h1 : a' = (g : MulAut L') ^ α.val := by
      have := congrArg Subtype.val hEq
      simpa using this
    rw [h1]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  obtain ⟨hcomp, hlay, hcentEnd⟩ := centEnd_of_node hM (hν g).1 hτ hBig hcent
  have hSne : SmallU.cls (ν g) s ≠ Finset.univ := by
    intro h
    have hc' : c₀ ∈ SmallU.cls (ν g) s := by
      rw [h]
      exact Finset.mem_univ _
    exact hc₀ ((SmallU.mem_cls.mp hc').trans (hs1 g))
  have hg1 : (g : MulAut L') ≠ 1 := by
    intro h
    apply hc₀
    have hg' : g = 1 := Subtype.ext (by simpa using h)
    rw [hg', map_one]
    rfl
  have hbigcard : 25920 < Nat.card (blockSU (K := K) (n := n) (SmallU.cls (ν g) s)) := by
    have hh : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
    rw [← Nat.card_congr (TableBUE.blockSUEquiv (SmallU.cls (ν g) s) hh).toEquiv]
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · have h9 := hd9 (by omega)
      exact IOneU.suCard_gt_of_five_le hh (by omega) (m := (SmallU.cls (ν g) s).card)
        (by omega)
    · exact IOneU.suCard_gt_of_two_le hh hn2 (m := (SmallU.cls (ν g) s).card) (by omega)
  have hnotsmall : ¬ LargeEvenSmall (LargeEvenLayer (ggFix (g : MulAut L'))) := by
    rw [hlay]
    exact not_largeEvenSmall_layer_of_node hM hker hZ hSne hbigcard
  obtain ⟨Usw, hUsw1, hUsw2, hUswA, -, hUswS⟩ :=
    SmallU.exists_swap_group hM hst hd3 hdiag hpair
  have hUle : Usw ≤ LargeEvenLayer (ggFix (g : MulAut L')) := by
    rw [hlay]
    exact hUswS _ hsS htS
  exact ⟨(g : MulAut L'), ⟨g.2, hg1, hcomp, hcentEnd⟩, fun _ _ => hnotsmall, Usw, hUle,
    hUsw1, hUsw2, hUswA⟩

theorem ggEndNodeRoot_unitaryDvd_of_ne
    {K : Type} [Field K] [Finite K]
    {n d p : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hdn : (d, n) ≠ (6, 1)) :
    GGEndNodeRoot p (ggUnitaryTorusRank p d) (UnitaryR K n d) (UnitaryI K n d) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα
  have hrk : ggUnitaryTorusRank p d = d - 3 := by
    simp [ggUnitaryTorusRank, hpd]
  rw [hrk] at hr
  obtain ⟨U, hU1, hU2, hAU⟩ := hα
  obtain ⟨φ, hM, hdiag⟩ : ∃ φ : ↥(unitarySU 2 n K d) →* L', UnitTB.Model φ ∧
      ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t := by
    by_cases h63 : d = 6 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := h63
      have hn2 : 2 ≤ n := by
        by_contra hcon
        exact hdn (by rw [show n = 1 by omega])
      exact Line63.exists_diagModel_frame hK hn2 hpq hψ hker hperf hA hAI (by simpa using hr)
        ⟨U, hU1, hU2, hAU⟩
    · exact SmallU.exists_model hK hn hd hp hpq hpd h63 hψ hker hperf hA hAI hr h3
  exact endNode_of_model hK hn hd hp hpq hpd hdn hM hψ hker hA hdiag hr hU1 hU2 hAU

theorem ggIOneUnitaryDvdRootInput_of_sixTwo
    (h : GGIOneUnitaryDvdRootSixTwoInput) : GGIOneUnitaryDvdRootInput := by
  intro K _ _ n d p hK hn hd hp hpq hpd
  by_cases hdn : (d, n) = (6, 1)
  · simp only [Prod.mk.injEq] at hdn
    obtain ⟨rfl, rfl⟩ := hdn
    exact h K p hK hp hpq hpd
  · exact ggEndNodeRoot_unitaryDvd_of_ne hK hn hd hp hpq hpd hdn

end CFSG.StandardType.IOneUDvdR

end
