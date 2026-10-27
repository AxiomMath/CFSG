module

public import CFSG.Quasithin.Background.FFC6U
public import CFSG.Quasithin.Background.SmithB57C
public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.H13.VolII16
public import CFSG.Quasithin.Background.B56Main
public import CFSG.Quasithin.Background.FFC7C
public import CFSG.Quasithin.Background.B1More13A

public section

namespace CFSG.Quasithin

namespace SmithB57

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank FFC FFC.B59
open scoped commutatorElement

section KCases

variable {V : Type} [CommGroup V] [Finite V]

theorem k_cases
    (hB51 : AsB51) (hB42 : AsB42) (hA21 : AsA21SQTKSection) {G A K : Subgroup (MulAut V)}
    (hc : B56Counterex G) (hmin : IsFFStarMin G A) (hK : CFSG.Open.IsComponentOf K G)
    (hKA : ⁅K, A⁆ = K) (hnoK : ¬ ThreeRank2 ↥K) :
    A ≤ K ∨ Nat.card A = 2 ∨
      ((∃ k, Odd k ∧ BinaryNaturalSL K (commSub (fixV (pCoreOf 2 (K ⊔ A))) K) ⊥ 3 k) ∧
        ∀ a ∈ A, ∃ x ∈ K, ∀ u ∈ commSub (fixV (pCoreOf 2 (K ⊔ A))) K, a u = x u) := by
  have hV := hc.hV
  have hb : B53Hyp G := hc.hyp
  have hO2 : pCoreOf 2 G = ⊥ := hb.1
  have hnG : G ≤ Subgroup.normalizer (K : Set (MulAut V)) :=
    B55.normalizes_comp B15P4.asB15Part4 hV hb.2.1 hK
  have hn : ∀ g ∈ G, ∀ l ∈ K, g * l * g⁻¹ ∈ K := fun g hg l hl =>
    B19Aux.conj_mem_of_le_normalizer hnG hg hl
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hK hmin.1 hKA
  have hLU : K ≤ stabSub (W0 K A) := le_sup_left.trans hst
  have hAU : A ≤ stabSub (W0 K A) := le_sup_right.trans hst
  have hfaithL := faithL hV hO2 hK hmin hKA
  obtain ⟨-, -, -, hLbH, -, hHb2, hoff, -, -⟩ := red_aut hV hK hmin.1 hKA
  have hno : ¬ ThreeRank2 ↥(Kr K A) := fun h =>
    hnoK (h.of_mulEquiv (resEquiv hLU hfaithL).symm)
  have hb51 : B51Hyp (Xr K A) (Kr K A) := b51Hyp_red hA21 hV hO2 hb hK hmin.1 hKA
  have hVM : ∀ v : ↥(W0 K A), v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  obtain ⟨P1, P2, -, -, P5, -⟩ := hB51 ↥(W0 K A) hVM (Xr K A) (Kr K A) hb51
  have hne : Xr K A ≠ ⊥ := fun h => hoff.2.1 (le_bot_iff.1 (h ▸ hoff.1))
  have hnoX : ¬ ThreeRank2 ↥(Xr K A) := fun h => hno (threeRank2_sq hHb2 h)
  obtain ⟨-, hcases⟩ := P1
  rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨hirr, hcl⟩ := classify_i b58Inputs hb51.2.2.2.2.2 hne hLbH hHb2 hno P2 P5 hi
    rcases hcl with ⟨hXK, hα, hnat⟩ | ⟨hXK, m, hm, hnat3⟩ | ⟨hXK, hα, hfc, hS⟩
    · exact Or.inl (caseA b58Inputs hB42 hV hO2 hmin hK hKA hn hno hb51 hXK hirr hα hnat).2.1.1
    · by_cases hC : fixV (Kr K A) ⊓ commV (Kr K A) = ⊥
      ·
        right; right
        have hĀK : Ar K A ≤ Kr K A := hXK ▸ hoff.1
        rw [hC] at hnat3
        refine ⟨⟨m, hm, binaryNaturalSL_map_bot hLU hfaithL hnat3⟩, fun a ha => ?_⟩
        obtain ⟨l, hl, hal⟩ := exists_eq_on_of_le hAU hĀK ha
        exact ⟨l, hl, fun u hu =>
          hal u (commSub_le_of_invariant (fun x hx w hw => (hLU hx w).2 hw) hu)⟩
      · have hm1 : m = 1 := by
          by_contra hne1
          have hm2 : 1 < m := by
            obtain ⟨k, hk⟩ := hm
            omega
          exact hC (H13.VolI.asI16Cover_holds ↥(W0 K A) hVM (Kr K A) hirr (Or.inl ⟨m, hm2, hnat3⟩))
        subst hm1
        have hα : commV (Kr K A) ⊔ fixV (Kr K A) = ⊤ := by
          rcases P5 with h | ⟨-, -, h⟩
          · rw [hXK] at h
            exact h
          · exact absurd (h hnat3) hC
        have hle := card_commV_le_sixteen hVM hirr hnat3
        have hcard := card_commV_eq_sixteen hnat3 hC hle
        exact Or.inl (caseV hV hO2 hmin hK hKA hn hXK hirr hα hnat3 hcard).2.1
    · exact Or.inr (Or.inl (caseB hV hO2 hmin hK hKA hn hXK hα hfc hS).2.1)
  · exact Or.inl (caseD hV hO2 hmin hK hKA hn hno P5 hii).2.1
  · exact (false_of_case_iii hLbH hnoX hiii.2).elim
  · exact (false_of_case_iv hLbH hnoX hiv.2).elim

end KCases

section Components

variable {Ω : Type*} [Group Ω] [Finite Ω]

theorem comp_commute {G L K : Subgroup Ω} (hL : CFSG.Open.IsComponentOf L G)
    (hK : CFSG.Open.IsComponentOf K G) (hLK : L ≠ K) : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l := by
  have hcomm : ⁅L, K⁆ = ⊥ := by
    rcases B113.component_le_or_commutator_eq_bot hL hK.2.1 with h1 | h1
    · rcases B113.component_le_or_commutator_eq_bot hK hL.2.1 with h2 | h2
      · exact absurd (le_antisymm h1 h2) hLK
      · rw [Subgroup.commutator_comm]
        exact h2
    · exact h1
  intro l hl x hx
  have : ⁅l, x⁆ ∈ ⁅L, K⁆ := Subgroup.commutator_mem_commutator hl hx
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

end Components

section Fitting

variable {V : Type} [CommGroup V] [Finite V]

theorem comp_commute_fitting {G L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L G) :
    ∀ l ∈ L, ∀ f ∈ fittingOf G, l * f = f * l := by
  have hXG : fittingOf G ≤ G := fittingOf_le G
  have hXn : ((fittingOf G).subgroupOf G).Normal := by
    have : (fittingOf G).subgroupOf G = CFSG.fittingSubgroup ↥G :=
      Subgroup.comap_map_eq_self_of_injective G.subtype_injective _
    rw [this]
    infer_instance
  have hXs : CFSG.Open.IsSubnormal (fittingOf G) G :=
    CFSG.Open.IsSubnormal.step hXG hXn (CFSG.Open.IsSubnormal.refl G)
  have hcomm : ⁅L, fittingOf G⁆ = ⊥ := by
    rcases B113.component_le_or_commutator_eq_bot hL hXs with h | h
    · exfalso
      have hLo : CFSG.Open.IsQuasisimple ↥L := hL.2.2
      have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
      have hperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
      have hnil : Group.IsNilpotent ↥(fittingOf G) := fittingOf_nilpotent G
      have h1 : Group.IsNilpotent ↥(L.subgroupOf (fittingOf G)) := inferInstance
      have h2 : Group.IsNilpotent ↥L :=
        (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe h)).mp h1
      exact Group.IsPerfect.not_isNilpotent ↥L h2
    · exact h
  intro l hl f hf
  have : ⁅l, f⁆ ∈ ⁅L, fittingOf G⁆ := Subgroup.commutator_mem_commutator hl hf
  rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem eq_one_of_centralizes {G : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥) {e : MulAut V}
    (heG : e ∈ G) (he2 : e * e = 1) (hF : ∀ f ∈ fittingOf G, e * f = f * e)
    (hcomp : ∀ K, CFSG.Open.IsComponentOf K G → ∀ x ∈ K, e * x = x * e) : e = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := Subgroup.zpowers e with hY
  have he2' : e ^ 2 = 1 := by rw [sq]; exact he2
  have hY2 : IsPGroup 2 ↥Y := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hk, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, he2', one_zpow]
  have hFe : quasithinGenFitting G ≤ Subgroup.centralizer ({e} : Set (MulAut V)) := by
    unfold quasithinGenFitting
    refine sup_le (sSup_le fun N hN x hx => ?_) (sSup_le fun K hK x hx => ?_)
    · have hxF : x ∈ fittingOf G := B56.le_fittingOf_of_nilpotent_normal hN.1 hN.2.1 hN.2.2 hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hF x hxF).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomp K hK x hx).symm
  have hec : e ∈ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hFe hx)
  have hYc : Y ≤ Subgroup.centralizer (quasithinGenFitting G : Set (MulAut V)) :=
    Subgroup.zpowers_le.mpr hec
  have hYL : Y ≤ quasithinGenFitting G :=
    Subgroup.zpowers_le.mpr (centralizer_quasithinGenFitting_le G ⟨heG, hec⟩)
  have hYb := B1More.eq_bot_of_le_center_genFitting hO2 hY2 hYL hYc
  have : e ∈ Y := Subgroup.mem_zpowers e
  rw [hYb, Subgroup.mem_bot] at this
  exact this

end Fitting

section Natural

variable {V : Type} [CommGroup V] [Finite V]

theorem not_threeRank2_of_comm {G L K : Subgroup (MulAut V)} (hq : IsQuotientOfSQTKTauCeti ↥G)
    (hLG : L ≤ G) (hKG : K ≤ G) (hS3 : FFC.S3Elems ↥L)
    (hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l) : ¬ ThreeRank2 ↥K := by
  rintro ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩
  obtain ⟨t, c, ht2, ht1, hc3, hc1, htc⟩ := hS3
  refine FFC.false_of_commuting_threes hq (t := (t : MulAut V)) (c := (c : MulAut V))
    (x := (x : MulAut V)) (y := (y : MulAut V)) (hLG t.2) (hLG c.2) (hKG x.2) (hKG y.2)
    (congrArg Subtype.val ht2) (fun h => ht1 (Subtype.ext h))
    (by simpa using congrArg Subtype.val hc3) (fun h => hc1 (Subtype.ext h))
    (by simpa using congrArg Subtype.val htc) (fun h => hx1 (Subtype.ext h))
    (by simpa using congrArg Subtype.val hx3) (by simpa using congrArg Subtype.val hy3)
    (congrArg Subtype.val hxy) ?_ (hLK _ t.2 _ x.2).symm (hLK _ c.2 _ x.2).symm
    (hLK _ t.2 _ y.2).symm (hLK _ c.2 _ y.2).symm
  intro hmem
  apply hyx
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by simpa using hn)⟩

theorem natural_data {L : Subgroup (MulAut V)} {U : Subgroup V} {m : ℕ}
    (h : BinaryNaturalSL L U ⊥ 3 m) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ m ∧
      Nonempty (↥(Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥L) ∧ rk U = 3 * m ∧
      (∀ l ∈ L, l ≠ 1 → rk ↥(U ⊓ fixV (Subgroup.zpowers l)) ≤ 2 * m) ∧
      (∀ l ∈ L, (∀ u ∈ U, l u = u) → l = 1) ∧ (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) := by
  have hfaith := B510.faithful_of_binaryNatural h
  obtain ⟨F, hFf, hfin, hc, π, hπ⟩ := h
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hc
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hsurj : Function.Surjective π := hπ.1
  obtain ⟨f, hfs, hfk, hfe⟩ := FFC.exists_natMap hπ
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hfk u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hUL : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U := fun l hl u hu => hπ.2.2.2.1 ⟨l, hl⟩ u hu
  refine ⟨F, hFf, inferInstance, hFc, ⟨MulEquiv.ofBijective π ⟨hinj, hsurj⟩⟩, ?_, ?_, hfaith,
    hUL⟩
  · have hcard : Nat.card U = 2 ^ (3 * m) := by
      rw [Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfs⟩), Nat.card_congr Multiplicative.toAdd,
        Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hFc, ← pow_mul, mul_comm]
    unfold rk
    rw [hcard, padicValNat.prime_pow]
  · intro l hl hl1
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(Assembly.LowTwoRank.StatedSL 3 F), π γ = ⟨l, hl⟩ :=
      hsurj ⟨l, hl⟩
    have hγ1 : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
      intro h1
      apply hl1
      have hγ' : γ = 1 := Subtype.ext (Units.ext h1)
      have h2 : (⟨l, hl⟩ : ↥L) = 1 := by
        rw [← hγ, hγ']
        exact map_one π
      exact congrArg Subtype.val h2
    have hle : Nat.card ↥(U ⊓ fixV (Subgroup.zpowers l)) ≤
        Nat.card (fixSub ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
      refine Nat.card_le_card_of_injective
        (fun u => ⟨Multiplicative.toAdd (f ⟨u.1, u.2.1⟩), ?_⟩) ?_
      · rw [mem_fixSub]
        have hu : l u.1 = u.1 := mem_fixV_zpowers.mp u.2.2
        have hu' : ((π γ : ↥L) : MulAut V) (u.1 : V) ∈ U := by
          rw [hγ]
          show l u.1 ∈ U
          rw [hu]
          exact u.2.1
        have h1 := hfe γ ⟨u.1, u.2.1⟩ hu'
        have h2 : (⟨((π γ : ↥L) : MulAut V) (u.1 : V), hu'⟩ : ↥U) = ⟨u.1, u.2.1⟩ := by
          apply Subtype.ext
          show ((π γ : ↥L) : MulAut V) (u.1 : V) = u.1
          rw [hγ]
          exact hu
        have h1' := (congrArg f h2).symm.trans h1
        have h3 := congrArg Multiplicative.toAdd h1'
        exact h3.symm
      · intro u v huv
        have h1 : f ⟨u.1, u.2.1⟩ = f ⟨v.1, v.2.1⟩ := by
          have := congrArg Subtype.val huv
          exact Multiplicative.toAdd.injective this
        have h2 := hfinj h1
        exact Subtype.ext (congrArg (fun x : ↥U => (x : V)) h2)
    have h2 := card_fixSub_le hγ1
    rw [hFc, ← pow_mul] at h2
    have h3 := hle.trans h2
    have h4 : 2 ^ rk ↥(U ⊓ fixV (Subgroup.zpowers l)) ≤ 2 ^ (m * 2) :=
      (Nat.le_of_dvd Nat.card_pos pow_padicValNat_dvd).trans h3
    have h5 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
    omega

end Natural

section Commutators

variable {V : Type} [CommGroup V]

omit [CommGroup V] in
theorem comm_identity {W : Type} [CommGroup W] (u a b c d : W) :
    u * a * (b * c) * (u * b * (a * d))⁻¹ = c * d⁻¹ := by
  rw [mul_inv_eq_iff_eq_mul]
  simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel, mul_one]

theorem commV_le_commSub_commV {L : Subgroup (MulAut V)} (hperf : ⁅L, L⁆ = L) :
    commV L ≤ commSub (commV L) L := by
  set W := commV L with hW
  set N := commSub W L with hN
  have h1 : ∀ l ∈ L, ∀ v, l v * v⁻¹ ∈ W := fun l hl v => Subgroup.subset_closure ⟨l, hl, v, rfl⟩
  have hWL : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W := fun l hl w hw => by
    have := W.mul_mem (h1 l hl w) hw
    rwa [inv_mul_cancel_right] at this
  have h2 : ∀ l ∈ L, ∀ w ∈ W, l w * w⁻¹ ∈ N := fun l hl w hw =>
    Subgroup.subset_closure ⟨l, hl, w, hw, rfl⟩
  rw [B19.commV_le_iff]
  calc L = ⁅L, L⁆ := hperf.symm
    _ ≤ B19.commLeSub N := by
      rw [Subgroup.commutator_le]
      intro g hg h hh v
      set u := (h * g)⁻¹ v with hu
      have hv : v = h (g u) := by
        rw [hu, ← MulAut.mul_apply, MulAut.apply_inv_self]
      have key : ⁅g, h⁆ v * v⁻¹ = g (h u) * (h (g u))⁻¹ := by
        rw [hv, commutatorElement_def]
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      rw [key]
      set a := g u * u⁻¹ with ha
      set b := h u * u⁻¹ with hb
      have haW : a ∈ W := h1 g hg u
      have hbW : b ∈ W := h1 h hh u
      have hgu : g u = u * a := by rw [ha, mul_comm u, inv_mul_cancel_right]
      have hhu : h u = u * b := by rw [hb, mul_comm u, inv_mul_cancel_right]
      have hgb : g b = b * (g b * b⁻¹) := by rw [mul_comm b, inv_mul_cancel_right]
      have hha : h a = a * (h a * a⁻¹) := by rw [mul_comm a, inv_mul_cancel_right]
      have e1 : g (h u) = u * a * (b * (g b * b⁻¹)) := by rw [hhu, map_mul, hgu, ← hgb]
      have e2 : h (g u) = u * b * (a * (h a * a⁻¹)) := by rw [hgu, map_mul, hhu, ← hha]
      rw [e1, e2, comm_identity]
      exact N.mul_mem (h2 g hg b hbW) (N.inv_mem (h2 h hh a haW))

theorem commV_le_of_sup {L A : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W) (hAW : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hLA : ⁅L, A⁆ = L) (hsup : W ⊔ fixV A = ⊤) : commV L ≤ W := by
  have hAle : A ≤ B19.commLeSub W := by
    intro a ha v
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 (hsup ▸ (Subgroup.mem_top v))
    have : a (w * c) * (w * c)⁻¹ = a w * w⁻¹ := by
      rw [map_mul, hc a ha]; simp [mul_comm]
    rw [this]
    exact W.mul_mem (hAW a ha w hw) (W.inv_mem hw)
  rw [B19.commV_le_iff, ← hLA, Subgroup.commutator_le]
  intro l hl a ha
  have h1 : l * a * l⁻¹ ∈ B19.commLeSub W := by
    intro v
    have e : (l * a * l⁻¹) v * v⁻¹ = l (a (l⁻¹ v) * (l⁻¹ v)⁻¹) := by
      simp [MulAut.mul_apply, map_mul, map_inv]
    rw [e]
    exact hLW l hl _ (hAle ha (l⁻¹ v))
  have h2 : a⁻¹ ∈ B19.commLeSub W := (B19.commLeSub W).inv_mem (hAle ha)
  have := (B19.commLeSub W).mul_mem h1 h2
  simpa [commutatorElement_def, mul_assoc] using this

theorem fix_commV_symm {L K : Subgroup (MulAut V)} (hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l)
    (h : ∀ l ∈ L, ∀ w ∈ commV K, l w = w) : ∀ x ∈ K, ∀ w ∈ commV L, x w = w := by
  have hle : commV L ≤ fixV K := by
    rw [B19.commV_le_iff]
    intro l hl v x hx
    have hxv : x v * v⁻¹ ∈ commV K := Subgroup.subset_closure ⟨x, hx, v, rfl⟩
    have h1 : l (x v * v⁻¹) = x v * v⁻¹ := h l hl _ hxv
    have h2 : x (l v) = l (x v) := by rw [← MulAut.mul_apply, ← hLK l hl x hx, MulAut.mul_apply]
    have h3 : l (x v) = l v * (x v * v⁻¹) := by
      calc l (x v) = l (v * (x v * v⁻¹)) := by rw [mul_comm v, inv_mul_cancel_right]
        _ = l v * l (x v * v⁻¹) := map_mul _ _ _
        _ = l v * (x v * v⁻¹) := by rw [h1]
    rw [map_mul, map_inv, h2, h3]
    simp only [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel, one_mul]
  intro x hx w hw
  exact hle hw x hx

end Commutators

section Case4

variable {V : Type} [CommGroup V] [Finite V]

theorem case4_data {G A X : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hmin : IsFFStarMin G A) (hX : CFSG.Open.IsComponentOf X G) (hXA : ⁅X, A⁆ = X)
    (hnat : ∃ m, Odd m ∧ BinaryNaturalSL X (commSub (fixV (pCoreOf 2 (X ⊔ A))) X) ⊥ 3 m)
    (hinner : ∀ a ∈ A, ∃ l ∈ X, ∀ u ∈ commSub (fixV (pCoreOf 2 (X ⊔ A))) X, a u = l u) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), Odd m ∧ Fintype.card F = 2 ^ m ∧
      Nonempty (↥(Assembly.LowTwoRank.StatedSL 3 F) ≃* ↥X) ∧
      rk (commSub (fixV (pCoreOf 2 (X ⊔ A))) X) = 3 * m ∧
      (∀ l ∈ X, l ≠ 1 →
        rk ↥(commSub (fixV (pCoreOf 2 (X ⊔ A))) X ⊓ fixV (Subgroup.zpowers l)) ≤ 2 * m) ∧
      (∀ l ∈ X, (∀ u ∈ commSub (fixV (pCoreOf 2 (X ⊔ A))) X, l u = u) → l = 1) ∧
      ∃ φ : ↥A →* ↥X,
        (∀ a : ↥A, ∀ u ∈ commSub (fixV (pCoreOf 2 (X ⊔ A))) X,
          (a : MulAut V) u = (φ a : MulAut V) u) ∧
        (∀ a : ↥A, ∀ x ∈ X, ((φ a : MulAut V)⁻¹ * a) * x = x * ((φ a : MulAut V)⁻¹ * a)) ∧
        (∀ w : V, (∀ a : ↥A, ((φ a : MulAut V)⁻¹ * a) w = w) →
          w ∈ fixV (pCoreOf 2 (X ⊔ A))) := by
  set W₀ := fixV (pCoreOf 2 (X ⊔ A)) with hW₀
  set U := commSub W₀ X with hU
  obtain ⟨m, hm, hnat'⟩ := hnat
  obtain ⟨F, hFf, hFt, hF, ⟨πX⟩, hrk, hfix, hfaith, hUL⟩ := natural_data hnat'
  obtain ⟨φ, hφ⟩ := exists_lpart hUL hfaith hinner
  have hAnX : A ≤ Subgroup.normalizer (X : Set (MulAut V)) := le_normalizer_of_commutator_eq hXA
  obtain ⟨-, -, -, hst, -, -⟩ := red_basic hV hX hmin.1 hXA
  have hUW : U ≤ W₀ := commSub_le_of_invariant (fun x hx w hw => (hst (Subgroup.mem_sup_left hx)
    w).2 hw)
  have hcU : ∀ a : ↥A, ∀ u ∈ U, ((φ a : MulAut V)⁻¹ * a) u = u := by
    intro a u hu
    rw [MulAut.mul_apply, hφ a u hu, MulAut.inv_apply_self]
  refine ⟨m, F, hFf, hFt, hm, hF, ⟨πX⟩, hrk, hfix, hfaith, φ, hφ, ?_, ?_⟩
  · intro a x hx
    set c := (φ a : MulAut V)⁻¹ * a with hc
    have hcx : c * x * c⁻¹ ∈ X := by
      have h1 : (a : MulAut V) * x * (a : MulAut V)⁻¹ ∈ X :=
        B19Aux.conj_mem_of_le_normalizer hAnX a.2 hx
      have e : c * x * c⁻¹ = (φ a : MulAut V)⁻¹ * ((a : MulAut V) * x * (a : MulAut V)⁻¹) *
          (φ a : MulAut V) := by rw [hc]; group
      rw [e]
      exact X.mul_mem (X.mul_mem (X.inv_mem (φ a).2) h1) (φ a).2
    have hcinv : ∀ u ∈ U, c⁻¹ u = u := by
      intro u hu
      have := hcU a u hu
      rw [← hc] at this
      calc c⁻¹ u = c⁻¹ (c u) := by rw [this]
        _ = u := MulAut.inv_apply_self _ _ _
    have heq : c * x * c⁻¹ * x⁻¹ = 1 := by
      refine hfaith _ (X.mul_mem hcx (X.inv_mem hx)) (fun u hu => ?_)
      have hxu : x⁻¹ u ∈ U := hUL _ (X.inv_mem hx) u hu
      simp only [MulAut.mul_apply]
      rw [hcinv _ hxu, MulAut.apply_inv_self]
      exact hcU a u hu
    have h1 : c * x * c⁻¹ = x := by
      calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [heq, one_mul]
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [h1]
  · intro w hw q hq
    have hqXA : q ∈ X ⊔ A := CFSG.LieType.BorelTits.pCoreOf_le 2 (X ⊔ A) hq
    obtain ⟨l, hl, a', ha', rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hAnX).1 hqXA
    have hl1 : l * (φ ⟨a', ha'⟩ : MulAut V) = 1 := by
      refine hfaith _ (X.mul_mem hl (φ ⟨a', ha'⟩).2) (fun u hu => ?_)
      have h1 : (l * a') u = u := hUW hu _ hq
      rw [MulAut.mul_apply, ← hφ ⟨a', ha'⟩ u hu]
      exact h1
    have hl' : l = (φ ⟨a', ha'⟩ : MulAut V)⁻¹ := eq_inv_of_mul_eq_one_left hl1
    rw [hl']
    exact hw ⟨a', ha'⟩

end Case4

section Final

variable {V : Type} [CommGroup V] [Finite V]

theorem s3Elems_of_natural {X : Subgroup (MulAut V)} {U : Subgroup V} {m : ℕ}
    (h : BinaryNaturalSL X U ⊥ 3 m) : FFC.S3Elems ↥X := by
  obtain ⟨F, hFf, hFt, hF, ⟨π⟩, -⟩ := natural_data h
  have : CharP F 2 := charP_two_of_card hF
  exact FFC.s3Elems_statedSL_three.of_mulEquiv π

theorem false_of_three_S3 {G L K K' : Subgroup (MulAut V)} (hq : IsQuotientOfSQTKTauCeti ↥G)
    (hLG : L ≤ G) (hKG : K ≤ G) (hK'G : K' ≤ G) (hSL : FFC.S3Elems ↥L) (hSK : FFC.S3Elems ↥K)
    (hSK' : FFC.S3Elems ↥K') (hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l)
    (hLK' : ∀ l ∈ L, ∀ x ∈ K', l * x = x * l) (hKK' : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x) :
    False := by
  set M := K ⊔ K' with hM
  have hMc : M ≤ Subgroup.centralizer (L : Set (MulAut V)) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro l hl
    · exact hLK l hl x hx
    · exact hLK' l hl x hx
  have hLM : ∀ l ∈ L, ∀ x ∈ M, l * x = x * l := fun l hl x hx =>
    Subgroup.mem_centralizer_iff.mp (hMc hx) l hl
  obtain ⟨-, c, -, -, hc3, hc1, -⟩ := hSK
  obtain ⟨t', c', ht'2, ht'1, hc'3, hc'1, ht'c'⟩ := hSK'
  apply not_threeRank2_of_comm hq hLG (sup_le hKG hK'G) hSL hLM
  refine ⟨⟨c, Subgroup.mem_sup_left c.2⟩, ⟨c', Subgroup.mem_sup_right c'.2⟩,
    fun h => hc1 (Subtype.ext (congrArg (fun z : ↥M => (z : MulAut V)) h)), Subtype.ext ?_,
    Subtype.ext ?_,
    Subtype.ext (hKK' _ c.2 _ c'.2), ?_⟩
  · simpa using congrArg Subtype.val hc3
  · simpa using congrArg Subtype.val hc'3
  · intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hc'K : (c' : MulAut V) ∈ K := by
      have : (c' : MulAut V) = (c : MulAut V) ^ n := by
        have := congrArg Subtype.val hn
        simpa using this.symm
      rw [this]
      exact K.zpow_mem c.2 n
    have h1 : (t' : MulAut V) * c' * (t' : MulAut V)⁻¹ = c' := by
      rw [(hKK' _ hc'K _ t'.2).symm, mul_inv_cancel_right]
    have h2 : (t' : MulAut V) * c' * (t' : MulAut V)⁻¹ = (c' : MulAut V)⁻¹ := by
      simpa using congrArg Subtype.val ht'c'
    have h3 : (c' : MulAut V) * c' = 1 := by
      have h4 : (c' : MulAut V) = (c' : MulAut V)⁻¹ := h1.symm.trans h2
      calc (c' : MulAut V) * c' = (c' : MulAut V)⁻¹ * c' := by rw [← h4]
        _ = 1 := inv_mul_cancel _
    have h5 : (c' : MulAut V) ^ 3 = 1 := by simpa using congrArg Subtype.val hc'3
    apply hc'1
    apply Subtype.ext
    calc (c' : MulAut V) = (c' : MulAut V) ^ 3 * ((c' : MulAut V) * c')⁻¹ := by group
      _ = 1 := by rw [h5, h3, inv_one, one_mul]

end Final

section B59Last

variable {V : Type} [CommGroup V] [Finite V]

theorem card_le_of_offender {G A : Subgroup (MulAut V)} (hA : IsFFStarOffender G A) :
    Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have := hA.2.2.2 ⊥ bot_le
  rwa [B1.card_bot_mul_card_fixV] at this

theorem card_ne_two {G A L : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hmin : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hLA : ⁅L, A⁆ = L)
    (hperf : ⁅L, L⁆ = L) (hmov : ∃ a ∈ A, ∃ u ∈ commSub (fixV (pCoreOf 2 (L ⊔ A))) L, a u ≠ u)
    (hne : commV L ≠ commSub (fixV (pCoreOf 2 (L ⊔ A))) L) : Nat.card A ≠ 2 := by
  intro hA2
  set W₀ := fixV (pCoreOf 2 (L ⊔ A)) with hW₀
  obtain ⟨-, -, -, hst, -, hAnc⟩ := red_basic hV hL hmin.1 hLA
  have hLW : ∀ l ∈ L, ∀ w ∈ W₀, l w ∈ W₀ := fun l hl w hw =>
    (hst (Subgroup.mem_sup_left hl) w).2 hw
  have hAW : ∀ a ∈ A, ∀ w ∈ W₀, a w ∈ W₀ := fun a ha w hw =>
    (hst (Subgroup.mem_sup_right ha) w).2 hw
  have hWA : commSub W₀ A ≠ ⊥ := by
    intro h
    apply hAnc
    intro a ha u hu
    exact (commSub_eq_bot_iff.1 h) hu a ha
  have hAst : A ≤ stabSub W₀ := le_sup_right.trans hst
  have hVM : ∀ v : ↥W₀, v ^ 2 = 1 := B1.sq_eq_one_sub hV _
  have hUW : commSub W₀ L ≤ W₀ := commSub_le_of_invariant hLW
  have hns : ¬ IsStrongFFStarOffender (autSub G W₀) (autSub A W₀) := by
    rintro ⟨hoff, hr⟩
    rw [rAV_lt_one_iff hVM hoff.isA2] at hr
    have h1 := card_autSub_mul hAst
    have hcA : Nat.card (autSub A W₀) ≤ 2 := by
      rw [← hA2, ← h1]
      exact Nat.le_mul_of_pos_right _ Nat.card_pos
    have hne' : fixV (autSub A W₀) ≠ ⊤ := by
      intro htop
      obtain ⟨a, ha, u, hu, hau⟩ := hmov
      apply hau
      have hmem : (⟨u, hUW hu⟩ : ↥W₀) ∈ fixV (autSub A W₀) := htop ▸ Subgroup.mem_top _
      have := hmem (resHom W₀ ⟨a, hAst ha⟩) (mem_autSub.2 ⟨⟨a, hAst ha⟩, ha, rfl⟩)
      exact congrArg Subtype.val this
    have hidx : 2 ≤ (fixV (autSub A W₀)).index := by
      have h0 : (fixV (autSub A W₀)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h1' : (fixV (autSub A W₀)).index ≠ 1 := fun h => hne' (Subgroup.index_eq_one.mp h)
      omega
    have h2 := (fixV (autSub A W₀)).card_mul_index
    have : Nat.card (autSub A W₀) * Nat.card (fixV (autSub A W₀)) ≤ Nat.card ↥W₀ := by
      calc Nat.card (autSub A W₀) * Nat.card (fixV (autSub A W₀)) ≤
          2 * Nat.card (fixV (autSub A W₀)) := Nat.mul_le_mul_right _ hcA
        _ ≤ (fixV (autSub A W₀)).index * Nat.card (fixV (autSub A W₀)) :=
          Nat.mul_le_mul_right _ hidx
        _ = Nat.card ↥W₀ := by rw [mul_comm]; exact h2
    omega
  have hsup := ((B1_5_2 hV hmin hAW hWA).2 hns).1
  have h1 : commV L ≤ W₀ := commV_le_of_sup hLW hAW hLA hsup
  apply hne
  refine le_antisymm ?_ ?_
  · exact (commV_le_commSub_commV hperf).trans (commSub_mono h1 le_rfl)
  · rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl

omit [Finite V] in
theorem psi_sq {L A : Subgroup (MulAut V)} (hAel : IsElemAbelian2 A) (φ : ↥A →* ↥L) (a : ↥A)
    (hc : ∀ x ∈ L, ((φ a : MulAut V)⁻¹ * a) * x = x * ((φ a : MulAut V)⁻¹ * a)) :
    ((φ a : MulAut V)⁻¹ * a) * ((φ a : MulAut V)⁻¹ * a) = 1 := by
  have ha2 : a * a = 1 := Subtype.ext (by simpa [sq] using hAel.2 a a.2)
  have hφ2 : (φ a : MulAut V) * φ a = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, ha2, map_one, Subgroup.coe_one]
  have h1 := hc _ (L.inv_mem (φ a).2)
  calc ((φ a : MulAut V)⁻¹ * a) * ((φ a : MulAut V)⁻¹ * a) =
      (((φ a : MulAut V)⁻¹ * a) * (φ a : MulAut V)⁻¹) * a := by group
    _ = ((φ a : MulAut V)⁻¹ * ((φ a : MulAut V)⁻¹ * a)) * a := by rw [h1]
    _ = ((φ a : MulAut V) * φ a)⁻¹ * ((a : MulAut V) * a) := by group
    _ = 1 := by
      rw [hφ2, inv_one, one_mul]
      exact congrArg Subtype.val ha2

theorem b59Last_holds
    (hB51 : AsB51) (hB42 : AsB42) (hA21 : AsA21SQTKSection) : FFC.B59Last := by
  intro V _ _ G hc A L hmin hL hLA hnat hinner
  by_contra hne
  have hV := hc.hV
  have hb : B53Hyp G := hc.hyp
  have hO2 : pCoreOf 2 G = ⊥ := hb.1
  have hq : IsQuotientOfSQTKTauCeti ↥G := isQuotientOfSQTKTauCeti_of_b53 hb
  have hAG : A ≤ G := hmin.1.1
  have hAel : IsElemAbelian2 A := hmin.1.2.2.1
  have hcent : A ≤ Subgroup.centralizer (fittingOf G : Set (MulAut V)) :=
    FFC.asB58 V G hc A hmin
  have hoff := card_le_of_offender hmin.1
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := ⟨hLq.1⟩
    exact Subgroup.commutator_eq_self
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hnG : ∀ X, CFSG.Open.IsComponentOf X G → ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X :=
    fun X hX g hg x hx => B19Aux.conj_mem_of_le_normalizer
      (B55.normalizes_comp B15P4.asB15Part4 hV hb.2.1 hX) hg hx
  have hAL : ¬ ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
    intro h
    have h0 : ⁅L, A⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro l hl a ha
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (h a ha l hl).symm
    exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt (hLA ▸ h0)
  obtain ⟨m, F, hFf, hFt, hm, hF, ⟨πL⟩, hUrk, hUfix, hfaith, φ, hφU, hψL, hW0⟩ :=
    case4_data hV hmin hL hLA hnat hinner
  have : CharP F 2 := charP_two_of_card hF
  have hSL : FFC.S3Elems ↥L := FFC.s3Elems_statedSL_three.of_mulEquiv πL
  set U := commSub (fixV (pCoreOf 2 (L ⊔ A))) L with hU
  have hψG : ∀ a : ↥A, (φ a : MulAut V)⁻¹ * a ∈ G := fun a =>
    G.mul_mem (G.inv_mem (hL.1 (φ a).2)) (hAG a.2)
  have hψsq : ∀ a : ↥A, ((φ a : MulAut V)⁻¹ * a) * ((φ a : MulAut V)⁻¹ * a) = 1 :=
    fun a => psi_sq hAel φ a (hψL a)
  have hψF : ∀ a : ↥A, ∀ f ∈ fittingOf G, ((φ a : MulAut V)⁻¹ * a) * f =
      f * ((φ a : MulAut V)⁻¹ * a) := by
    intro a f hf
    have h1 : (a : MulAut V) * f = f * a :=
      (Subgroup.mem_centralizer_iff.mp (hcent a.2) f hf).symm
    have h2 : (φ a : MulAut V)⁻¹ * f = f * (φ a : MulAut V)⁻¹ :=
      comp_commute_fitting hL _ (L.inv_mem (φ a).2) f hf
    calc (φ a : MulAut V)⁻¹ * a * f = (φ a : MulAut V)⁻¹ * (a * f) := by group
      _ = (φ a : MulAut V)⁻¹ * (f * a) := by rw [h1]
      _ = ((φ a : MulAut V)⁻¹ * f) * a := by group
      _ = f * (φ a : MulAut V)⁻¹ * a := by rw [h2]
      _ = f * ((φ a : MulAut V)⁻¹ * a) := by group
  have hAU : ∃ a : ↥A, φ a ≠ 1 := by
    by_contra h
    push Not at h
    apply hAL
    intro a ha l hl
    have h1 := hψL ⟨a, ha⟩ l hl
    rw [h ⟨a, ha⟩, Subgroup.coe_one, inv_one, one_mul] at h1
    exact h1
  have hmov : ∃ a ∈ A, ∃ u ∈ U, a u ≠ u := by
    obtain ⟨a, ha⟩ := hAU
    by_contra h
    push Not at h
    apply ha
    apply Subtype.ext
    refine hfaith _ (φ a).2 (fun u hu => ?_)
    rw [← hφU a u hu]
    exact h a a.2 u hu
  have hA2 : Nat.card A ≠ 2 := card_ne_two hV hmin hL hLA hLperf hmov hne
  have hAC : ∃ a : ↥A, ∃ w ∈ commV L, ((φ a : MulAut V)⁻¹ * a) w ≠ w := by
    by_contra h
    push Not at h
    apply hne
    have h1 : commV L ≤ fixV (pCoreOf 2 (L ⊔ A)) := fun w hw => hW0 w (fun a => h a w hw)
    refine le_antisymm ((commV_le_commSub_commV hLperf).trans (commSub_mono h1 le_rfl)) ?_
    rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  obtain ⟨K, hK, hKL, a₁, x₁, hx₁K, hx₁⟩ : ∃ K, CFSG.Open.IsComponentOf K G ∧ K ≠ L ∧
      ∃ a : ↥A, ∃ x ∈ K, ((φ a : MulAut V)⁻¹ * a) * x ≠ x * ((φ a : MulAut V)⁻¹ * a) := by
    by_contra h
    push Not at h
    obtain ⟨a, w, hw, hwa⟩ := hAC
    apply hwa
    have h1 : (φ a : MulAut V)⁻¹ * a = 1 := by
      refine eq_one_of_centralizes hO2 (hψG a) (hψsq a) (hψF a) (fun X hX x hx => ?_)
      by_cases hXL : X = L
      · subst hXL
        exact hψL a x hx
      · exact h X hX hXL a x hx
    rw [h1, MulAut.one_apply]
  have hKG : K ≤ G := hK.1
  have hLK : ∀ l ∈ L, ∀ x ∈ K, l * x = x * l := comp_commute hL hK (Ne.symm hKL)
  have hKA : ⁅K, A⁆ = K := by
    rcases B1Red.commutator_eq_or_commute (Or.inl hK.2.2)
      (fun a ha k hk => hnG K hK a (hAG ha) k hk) with h | h
    · exact h
    · exfalso
      apply hx₁
      have h1 : (a₁ : MulAut V) * x₁ = x₁ * a₁ := h a₁ a₁.2 x₁ hx₁K
      have h2 := hLK _ (L.inv_mem (φ a₁).2) x₁ hx₁K
      calc (φ a₁ : MulAut V)⁻¹ * a₁ * x₁ = (φ a₁ : MulAut V)⁻¹ * (a₁ * x₁) := by group
        _ = (φ a₁ : MulAut V)⁻¹ * (x₁ * a₁) := by rw [h1]
        _ = ((φ a₁ : MulAut V)⁻¹ * x₁) * a₁ := by group
        _ = x₁ * (φ a₁ : MulAut V)⁻¹ * a₁ := by rw [h2]
        _ = x₁ * ((φ a₁ : MulAut V)⁻¹ * a₁) := by group
  have hcase : ∀ X, CFSG.Open.IsComponentOf X G → X ≠ L → ⁅X, A⁆ = X →
      (∃ k, Odd k ∧ BinaryNaturalSL X (commSub (fixV (pCoreOf 2 (X ⊔ A))) X) ⊥ 3 k) ∧
        ∀ a ∈ A, ∃ x ∈ X, ∀ u ∈ commSub (fixV (pCoreOf 2 (X ⊔ A))) X, a u = x u := by
    intro X hX hXL hXA
    have hLX := comp_commute hL hX (Ne.symm hXL)
    have hno : ¬ ThreeRank2 ↥X := not_threeRank2_of_comm hq hL.1 hX.1 hSL hLX
    rcases k_cases hB51 hB42 hA21 hc hmin hX hXA hno with h | h | h
    · exfalso
      apply hAL
      intro a ha l hl
      exact (hLX l hl a (h ha)).symm
    · exact absurd h hA2
    · exact h
  obtain ⟨hnatK, hinnerK⟩ := hcase K hK hKL hKA
  obtain ⟨k, F', hF'f, hF't, hk, hF', ⟨πK⟩, hUKrk, hUKfix, hfaithK, φK, hφKU, hψK, hW0K⟩ :=
    case4_data hV hmin hK hKA hnatK hinnerK
  have : CharP F' 2 := charP_two_of_card hF'
  have hSK : FFC.S3Elems ↥K := FFC.s3Elems_statedSL_three.of_mulEquiv πK
  have hφKa : ∀ a : ↥A, (φK a : MulAut V) * a = a * φK a := by
    intro a
    have h1 := hψK a _ (φK a).2
    calc (φK a : MulAut V) * a = (φK a : MulAut V) * ((φK a : MulAut V) *
        ((φK a : MulAut V)⁻¹ * a)) := by group
      _ = (φK a : MulAut V) * (((φK a : MulAut V)⁻¹ * a) * (φK a : MulAut V)) := by rw [h1]
      _ = a * φK a := by group
  have hφK2 : ∀ a : ↥A, (φK a : MulAut V) * φK a = 1 := by
    intro a
    have ha2 : a * a = 1 := Subtype.ext (by simpa [sq] using hAel.2 a a.2)
    rw [← Subgroup.coe_mul, ← map_mul, ha2, map_one, Subgroup.coe_one]
  have hψeq : ∀ a : ↥A, (φ a : MulAut V)⁻¹ * a = φK a := by
    intro a
    set ψ := (φ a : MulAut V)⁻¹ * a with hψ
    set e := ψ * (φK a : MulAut V)⁻¹ with he
    have hcψ : ψ * φK a = φK a * ψ := by
      have h1 := hLK _ (L.inv_mem (φ a).2) _ (φK a).2
      calc ψ * φK a = (φ a : MulAut V)⁻¹ * (a * φK a) := by rw [hψ]; group
        _ = (φ a : MulAut V)⁻¹ * (φK a * a) := by rw [hφKa]
        _ = ((φ a : MulAut V)⁻¹ * φK a) * a := by group
        _ = φK a * (φ a : MulAut V)⁻¹ * a := by rw [h1]
        _ = φK a * ψ := by rw [hψ]; group
    have hφKa' : (a : MulAut V) * (φK a : MulAut V)⁻¹ = (φK a : MulAut V)⁻¹ * a := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hφKa, ← mul_assoc, inv_mul_cancel, one_mul]
    have hcψ' : (φK a : MulAut V)⁻¹ * ψ = ψ * (φK a : MulAut V)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hcψ, mul_assoc, mul_inv_cancel, mul_one]
    have he' : e = (φ a : MulAut V)⁻¹ * ((φK a : MulAut V)⁻¹ * a) := by
      rw [he, hψ, mul_assoc, hφKa']
    have he1 : e = 1 := by
      refine eq_one_of_centralizes hO2 (G.mul_mem (hψG a) (G.inv_mem (hKG (φK a).2))) ?_ ?_ ?_
      · calc e * e = (ψ * ψ) * ((φK a : MulAut V) * φK a)⁻¹ := by
              rw [he]
              calc ψ * (φK a : MulAut V)⁻¹ * (ψ * (φK a : MulAut V)⁻¹) =
                  ψ * ((φK a : MulAut V)⁻¹ * ψ) * (φK a : MulAut V)⁻¹ := by group
                _ = ψ * (ψ * (φK a : MulAut V)⁻¹) * (φK a : MulAut V)⁻¹ := by rw [hcψ']
                _ = (ψ * ψ) * ((φK a : MulAut V) * φK a)⁻¹ := by group
          _ = 1 := by rw [hψsq a, hφK2 a, inv_one, mul_one]
      · intro f hf
        have h1 := hψF a f hf
        have h2 : (φK a : MulAut V)⁻¹ * f = f * (φK a : MulAut V)⁻¹ :=
          comp_commute_fitting hK _ (K.inv_mem (φK a).2) f hf
        calc e * f = ψ * ((φK a : MulAut V)⁻¹ * f) := by rw [he]; group
          _ = ψ * (f * (φK a : MulAut V)⁻¹) := by rw [h2]
          _ = (ψ * f) * (φK a : MulAut V)⁻¹ := by group
          _ = f * ψ * (φK a : MulAut V)⁻¹ := by rw [h1]
          _ = f * e := by rw [he]; group
      · intro X hX x hx
        by_cases hXL : X = L
        · subst hXL
          have h1 := hψL a x hx
          have h2 : (φK a : MulAut V)⁻¹ * x = x * (φK a : MulAut V)⁻¹ :=
            (hLK x hx _ (K.inv_mem (φK a).2)).symm
          calc e * x = ψ * ((φK a : MulAut V)⁻¹ * x) := by rw [he]; group
            _ = ψ * (x * (φK a : MulAut V)⁻¹) := by rw [h2]
            _ = (ψ * x) * (φK a : MulAut V)⁻¹ := by group
            _ = x * ψ * (φK a : MulAut V)⁻¹ := by rw [h1]
            _ = x * e := by rw [he]; group
        by_cases hXK : X = K
        · subst hXK
          rw [he']
          have h1 := hψK a x hx
          have h2 : (φ a : MulAut V)⁻¹ * x = x * (φ a : MulAut V)⁻¹ :=
            hLK _ (L.inv_mem (φ a).2) x hx
          calc (φ a : MulAut V)⁻¹ * ((φK a : MulAut V)⁻¹ * a) * x =
              (φ a : MulAut V)⁻¹ * (((φK a : MulAut V)⁻¹ * a) * x) := by group
            _ = (φ a : MulAut V)⁻¹ * (x * ((φK a : MulAut V)⁻¹ * a)) := by rw [h1]
            _ = ((φ a : MulAut V)⁻¹ * x) * ((φK a : MulAut V)⁻¹ * a) := by group
            _ = x * (φ a : MulAut V)⁻¹ * ((φK a : MulAut V)⁻¹ * a) := by rw [h2]
            _ = x * ((φ a : MulAut V)⁻¹ * ((φK a : MulAut V)⁻¹ * a)) := by group
        have hLX := comp_commute hL hX (Ne.symm hXL)
        have hKX := comp_commute hK hX (Ne.symm hXK)
        rcases B1Red.commutator_eq_or_commute (Or.inl hX.2.2)
          (fun a ha k hk => hnG X hX a (hAG ha) k hk) with hXA | hXA
        · exfalso
          obtain ⟨hnatX, -⟩ := hcase X hX hXL hXA
          obtain ⟨j, -, hj⟩ := hnatX
          exact false_of_three_S3 hq hL.1 hKG hX.1 hSL hSK (s3Elems_of_natural hj) hLK hLX hKX
        · have h1 : (a : MulAut V) * x = x * a := hXA a a.2 x hx
          have h2 : (φ a : MulAut V)⁻¹ * x = x * (φ a : MulAut V)⁻¹ :=
            hLX _ (L.inv_mem (φ a).2) x hx
          have h3 : (φK a : MulAut V)⁻¹ * x = x * (φK a : MulAut V)⁻¹ :=
            hKX _ (K.inv_mem (φK a).2) x hx
          calc e * x = (φ a : MulAut V)⁻¹ * (a * ((φK a : MulAut V)⁻¹ * x)) := by
                rw [he, hψ]; group
            _ = (φ a : MulAut V)⁻¹ * (a * (x * (φK a : MulAut V)⁻¹)) := by rw [h3]
            _ = (φ a : MulAut V)⁻¹ * ((a * x) * (φK a : MulAut V)⁻¹) := by group
            _ = (φ a : MulAut V)⁻¹ * ((x * a) * (φK a : MulAut V)⁻¹) := by rw [h1]
            _ = ((φ a : MulAut V)⁻¹ * x) * a * (φK a : MulAut V)⁻¹ := by group
            _ = x * (φ a : MulAut V)⁻¹ * a * (φK a : MulAut V)⁻¹ := by rw [h2]
            _ = x * e := by rw [he, hψ]; group
    calc ψ = e * φK a := by rw [he]; group
      _ = φK a := by rw [he1, one_mul]
  have hφK_mem : ∀ a : ↥A, (φ a : MulAut V)⁻¹ * a ∈ K := fun a => by
    rw [hψeq a]
    exact (φK a).2
  have hnc : ¬ ∀ x ∈ K, ∀ w ∈ commV L, x w = w := by
    intro h
    obtain ⟨a, w, hw, hwa⟩ := hAC
    exact hwa (h _ (hφK_mem a) w hw)
  have hW0L : ∀ w : V, (∀ a : ↥A, ((φ a : MulAut V)⁻¹ * a) w = w) → ∀ l ∈ L, l w * w⁻¹ ∈ U :=
    fun w hw l hl => Subgroup.subset_closure ⟨l, hl, w, hW0 w hw, rfl⟩
  rcases le_total k m with hkm | hmk
  · exact counting_false hV hm hF hF' hkm πL πK hLq hK.2.2 hLK hAel hoff hUrk hUfix φ hφU
      hφK_mem hW0L hAU hnc
  · have hKL' : ∀ x ∈ K, ∀ l ∈ L, x * l = l * x := fun x hx l hl => (hLK l hl x hx).symm
    have hφL_mem : ∀ a : ↥A, (φK a : MulAut V)⁻¹ * a ∈ L := by
      intro a
      have h1 : (a : MulAut V) = φ a * φK a := by
        rw [← hψeq a]
        group
      have h2 := hLK _ (φ a).2 _ (φK a).2
      have h3 : (φK a : MulAut V)⁻¹ * a = φ a := by
        rw [h1, h2]
        group
      rw [h3]
      exact (φ a).2
    have hW0K' : ∀ w : V, (∀ a : ↥A, ((φK a : MulAut V)⁻¹ * a) w = w) → ∀ l ∈ K,
        l w * w⁻¹ ∈ commSub (fixV (pCoreOf 2 (K ⊔ A))) K :=
      fun w hw l hl => Subgroup.subset_closure ⟨l, hl, w, hW0K w hw, rfl⟩
    have hAUK : ∃ a : ↥A, φK a ≠ 1 := by
      obtain ⟨a, w, hw, hwa⟩ := hAC
      refine ⟨a, fun h => hwa ?_⟩
      rw [hψeq a, h, Subgroup.coe_one, MulAut.one_apply]
    have hncK : ¬ ∀ x ∈ L, ∀ w ∈ commV K, x w = w := fun h => hnc (fix_commV_symm hLK h)
    exact counting_false hV hk hF' hF hmk πK πL hK.2.2 hLq hKL' hAel hoff hUKrk hUKfix φK
      hφKU hφL_mem hW0K' hAUK hncK

end B59Last

end SmithB57

end CFSG.Quasithin
