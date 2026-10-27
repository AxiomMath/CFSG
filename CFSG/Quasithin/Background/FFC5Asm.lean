module

public import CFSG.Quasithin.Background.FFC5Idx
public import CFSG.Quasithin.Background.FFC5Dich
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.FFC4G2
public import CFSG.Quasithin.Background.FFC5Main

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Asm

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def B510OffendersAll : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G : Subgroup (MulAut V)), B56Counterex G →
    ∀ A L, IsFFStarMin G A → CFSG.Open.IsComponentOf L G → ⁅L, A⁆ = L → B59Conclusion A L →
      (B59Case1 A L ∨ B59Case3 A L ∨ B59Case4 A L ∨ B59Case5 A L → B510Offenders G L) ∧
        (B59Case2 A L → B510Offenders G (L ⊔ A))

@[expose] def B512Tail : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (G G₁ G₂ : Subgroup (MulAut V)), B56Counterex G →
    B510Fa G G₁ G₂ → G₂ ≠ ⊥ → BinaryNaturalSL G₁ (commV G₁) ⊥ 3 1 →
      (commV G₁ ⊔ fixV G₁).index = 2 → GoodFactor (autSub G₂ (fixV G₁)) → False

theorem finish_nonexc
    (hI : B58Inputs) {G G₁ G₂ : Subgroup (MulAut V)} (hc : B56Counterex G)
    (hs : B511Split G G₁ G₂) (hG₁ : G₁ ≠ ⊥)
    (pieces : (B56FactorList ↥G₁ ∧ B56Piece G₁ (commV G₁ ⊔ fixV G) (fixV G)) ∧ S3Elems ↥G₁)
    (hcase1 : G₂ = ⊥ → B56Case1 G) : False := by
  by_cases hG₂ : G₂ = ⊥
  · exact hc.not_cases (Or.inl (hcase1 hG₂))
  · exact hs.false_of_split hI hc hG₁ hG₂ pieces.2 pieces.1

omit [Finite V] in
theorem eq_of_bot {G G₁ G₂ : Subgroup (MulAut V)} (h : B510Data G G₁ G₂) (h2 : G₂ = ⊥) : G = G₁ := by
  rw [← h.sup, h2, sup_bot_eq]

omit [Finite V] in
theorem centralizes_of_normal {G L : Subgroup (MulAut V)}
    (hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hfaith : ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1) :
    ∀ c ∈ G, (∀ w ∈ commV L, c w = w) → ∀ x ∈ L, c * x = x * c := by
  intro c hc hcw x hx
  have hd : c * x * c⁻¹ * x⁻¹ ∈ L := L.mul_mem (hn c hc x hx) (L.inv_mem hx)
  have h1 : c * x * c⁻¹ * x⁻¹ = 1 := by
    apply hfaith _ hd
    intro w hw
    have hxw : (x⁻¹ : MulAut V) w ∈ commV L := commV_invariant_self L _ (L.inv_mem hx) w hw
    have hcinv : ∀ w' ∈ commV L, c⁻¹ w' = w' := fun w' hw' => by
      calc c⁻¹ w' = c⁻¹ (c w') := by rw [hcw w' hw']
        _ = w' := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl
    show c (x (c⁻¹ (x⁻¹ w))) = w
    rw [hcinv _ hxw]
    simp [hcw w hw]
  have : c * x = x * c := by
    have h2 := congrArg (fun y => y * x * c) h1
    simpa [mul_assoc] using h2
  exact this

omit [Finite V] in
theorem faithful_case1 {A L : Subgroup (MulAut V)} (h : B59Case1 A L) :
    ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1 := by
  obtain ⟨⟨n, K, hK, hf, hc, π, hπ⟩, -, -⟩ := h
  exact faithful_on_of_realizes (FFModel.nat_faithful _) hπ

omit [Finite V] in
theorem faithful_case3 {A L : Subgroup (MulAut V)} (h : B59Case3 A L) :
    ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1 := by
  obtain ⟨⟨m, K, hK, hf, -, hc, I, π, hZ, -, hsup, hreal⟩, -, -⟩ := h
  have hI0 : I 0 ≤ commV L := by
    rw [← hsup]
    exact le_trans le_rfl (le_trans (le_iSup I 0) le_sup_right)
  intro x hx hxw
  exact faithful_on_of_realizes (FFModel.nat_faithful _) (hreal 0) x hx fun u hu => hxw u (hI0 hu)

omit [Finite V] in
theorem faithful_case4 {A L : Subgroup (MulAut V)} (h : B59Case4 A L) :
    ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1 := by
  obtain ⟨⟨m, -, K, hK, hf, hc, π, hπ⟩, -⟩ := h
  exact faithful_on_of_realizes (FFModel.nat_faithful _) hπ

omit [Finite V] in
theorem faithful_case5 {A L : Subgroup (MulAut V)} (h : B59Case5 A L) :
    ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1 := by
  obtain ⟨-, -, -, ⟨-, ⟨K, hK, hf, hc, π, hπ⟩, -⟩, -⟩ := h
  exact faithful_on_of_realizes (FFModel.nat_faithful _) hπ

omit [Finite V] in
theorem nontrivial_of_component {G L : Subgroup (MulAut V)} (hL : CFSG.Open.IsComponentOf L G) :
    L ≠ ⊥ := by
  have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL.2.2
  exact (Subgroup.nontrivial_iff_ne_bot L).1 this

theorem case1_false
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hI : B58Inputs)
    {G : Subgroup (MulAut V)} (hc : B56Counterex G) {A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hOff : B510Offenders G L) (h : B59Case1 A L) : False := by
  have hJ : G = ffJ G := hc.hyp.2.1
  have hn' := B55.normalizes_comp hP4 hc.hV hJ hL
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn' hb hl
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hfaith := faithful_case1 h
  have hdata := b510_two hJ hL.1 hfaith (centralizes_of_normal hn hfaith) hOff
  have hs := hdata.toSplit (dich_case1 hc.hV h)
  obtain ⟨⟨n, hn1⟩, -, -⟩ := h
  exact finish_nonexc hI hc hs (nontrivial_of_component hL) (piece_case1 hs hn1)
    fun h2 => b56Case1_of_split hB51 hA21 hc hL.1 hn hLq
      (fun y hy => by rw [eq_of_bot hdata h2] at hy; exact L.pow_mem hy 2) (b56List_sl2 hn1)

theorem case3_false
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hI : B58Inputs)
    {G : Subgroup (MulAut V)} (hc : B56Counterex G) {A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hOff : B510Offenders G L)
    (h : B59Case3 A L) : False := by
  have hJ : G = ffJ G := hc.hyp.2.1
  have hn' := B55.normalizes_comp hP4 hc.hV hJ hL
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn' hb hl
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hfaith := faithful_case3 h
  have hdata := b510_two hJ hL.1 hfaith (centralizes_of_normal hn hfaith) hOff
  have hs := hdata.toSplit (dich_case3 hA.1.2.2.1 hA.1.2.1 h)
  obtain ⟨⟨m, K, hK, hf, hm, hcard, hd⟩, -, -⟩ := h
  exact finish_nonexc hI hc hs (nontrivial_of_component hL) (piece_case3 hs hm hcard hd)
    fun h2 => b56Case1_of_split hB51 hA21 hc hL.1 hn hLq
      (fun y hy => by rw [eq_of_bot hdata h2] at hy; exact L.pow_mem hy 2)
      (b56List_sl3_sum hcard hd)

theorem case5_false
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hI : B58Inputs)
    {G : Subgroup (MulAut V)} (hc : B56Counterex G) {A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hOff : B510Offenders G L)
    (h : B59Case5 A L) : False := by
  have hJ : G = ffJ G := hc.hyp.2.1
  have hn' := B55.normalizes_comp hP4 hc.hV hJ hL
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn' hb hl
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hfaith := faithful_case5 h
  have hdata := b510_two hJ hL.1 hfaith (centralizes_of_normal hn hfaith) hOff
  have hs := hdata.toSplit (dich_case5 hA.1.2.2.1 h)
  obtain ⟨hiso, -, -, ⟨-, hnat, -⟩, -⟩ := h
  exact finish_nonexc hI hc hs (nontrivial_of_component hL) (piece_case5 hs hiso hnat)
    fun h2 => b56Case1_of_split hB51 hA21 hc hL.1 hn hLq
      (fun y hy => by rw [eq_of_bot hdata h2] at hy; exact L.pow_mem hy 2)
      (b56List_sl3_two hiso)

omit [Finite V] in
theorem s3Elems_of_natural3 {L : Subgroup (MulAut V)} {U Z : Subgroup V} {m : ℕ}
    (h : BinaryNaturalSL L U Z 3 m) : S3Elems ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have : CharP K 2 := charP_two_of_card_pow hc
  exact s3Elems_statedSL_three.of_injective π hinj

theorem case4_false
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hI : B58Inputs)
    (hTail : B512Tail) {G : Subgroup (MulAut V)} (hc : B56Counterex G) {A L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L G) (hOff : B510Offenders G L) (h : B59Case4 A L) : False := by
  have hJ : G = ffJ G := hc.hyp.2.1
  have hn' := B55.normalizes_comp hP4 hc.hV hJ hL
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn' hb hl
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hfaith := faithful_case4 h
  have hdata := b510_two hJ hL.1 hfaith (centralizes_of_normal hn hfaith) hOff
  have hdich := dich_case4 h
  obtain ⟨⟨m, hm, hn1⟩, -⟩ := h
  have hcase1 : G ⊓ centSub (commV L) = ⊥ → B56Case1 G := fun h2 =>
    b56Case1_of_split hB51 hA21 hc hL.1 hn hLq
      (fun y hy => by rw [eq_of_bot hdata h2] at hy; exact L.pow_mem hy 2) (b56List_sl3 hn1)
  by_cases hG₂ : G ⊓ centSub (commV L) = ⊥
  · exact hc.not_cases (Or.inl (hcase1 hG₂))
  rcases hdich with hdec | ⟨hnat, hidx⟩
  · have hs := hdata.toSplit hdec
    exact finish_nonexc hI hc hs (nontrivial_of_component hL) (piece_case4 hs hm hn1) hcase1
  · have hfa : ∀ g ∈ G ⊓ centSub (commV L), (∀ v ∈ fixV L, g v = v) → g = 1 :=
      hdata.faithful_of_idx hc.hV hc.hyp.1 (le_of_eq hidx)
    have hFa := hdata.toFa hfa
    have hgood := hFa.good hI hc (nontrivial_of_component hL) hG₂ (s3Elems_of_natural3 hn1)
    exact hTail V G L _ hc hFa hG₂ hnat hidx hgood

theorem centralizes_case2 {G A L : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (hO2 : pCoreOf 2 G = ⊥) (hAG : A ≤ G)
    (hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hle : L ⊔ A ≤ B19.commLeSub (commV L))
    (hfaithL : ∀ x ∈ L, (∀ w ∈ commV L, x w = w) → x = 1) :
    ∀ c ∈ G, (∀ w ∈ commV L, c w = w) → ∀ x ∈ L ⊔ A, c * x = x * c := by
  have hWG : ∀ g ∈ G, ∀ w ∈ commV L, g w ∈ commV L := fun g hg w hw =>
    commV_invariant (fun x hx => hn g hg x hx) hw
  intro c hc hcw
  have hcinv : ∀ w' ∈ commV L, c⁻¹ w' = w' := fun w' hw' => by
    calc c⁻¹ w' = c⁻¹ (c w') := by rw [hcw w' hw']
      _ = w' := by rw [← MulAut.mul_apply, inv_mul_cancel]; rfl
  have hLc : L ≤ Subgroup.centralizer ({c} : Set (MulAut V)) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact centralizes_of_normal hn hfaithL c hc hcw x hx
  have hAc : A ≤ Subgroup.centralizer ({c} : Set (MulAut V)) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    set N : Subgroup (MulAut V) := G ⊓ centSub (commV L) ⊓ B19.commLeSub (commV L) with hN
    have hNG : N ≤ G := fun x hx => hx.1.1
    have hGN : ∀ g ∈ G, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
      intro g hg n hn'
      refine ⟨⟨G.mul_mem (G.mul_mem hg hn'.1.1) (G.inv_mem hg), fun w hw => ?_⟩, fun v => ?_⟩
      · have hw' : (g⁻¹ : MulAut V) w ∈ commV L := hWG g⁻¹ (G.inv_mem hg) w hw
        show g (n (g⁻¹ w)) = w
        rw [hn'.1.2 _ hw']
        simp
      · have h1 : (g * n * g⁻¹ : MulAut V) v * v⁻¹ = g (n (g⁻¹ v) * (g⁻¹ v)⁻¹) := by
          simp [MulAut.mul_apply]
        rw [h1]
        exact hWG g hg _ (hn'.2 (g⁻¹ v))
    have hle2 : N ≤ pCoreOf 2 G :=
      le_pCoreOf_of_trivial_sec hV hNG hGN (fun n hn' x hx => hn'.1.2 x hx)
        (fun n hn' v => hn'.2 v)
    rw [hO2, le_bot_iff] at hle2
    have hd : c * a * c⁻¹ * a⁻¹ ∈ N := by
      refine ⟨⟨G.mul_mem (G.mul_mem (G.mul_mem hc (hAG ha)) (G.inv_mem hc)) (G.inv_mem (hAG ha)),
        fun w hw => ?_⟩, ?_⟩
      · have haw : (a⁻¹ : MulAut V) w ∈ commV L := hWG a⁻¹ (G.inv_mem (hAG ha)) w hw
        show c (a (c⁻¹ (a⁻¹ w))) = w
        rw [hcinv _ haw]
        simp [hcw w hw]
      · have hca : c * a * c⁻¹ ∈ B19.commLeSub (commV L) := fun v => by
          have h1 : (c * a * c⁻¹ : MulAut V) v * v⁻¹ = c (a (c⁻¹ v) * (c⁻¹ v)⁻¹) := by
            simp [MulAut.mul_apply]
          rw [h1]
          exact hWG c hc _ (hle (Subgroup.mem_sup_right ha) (c⁻¹ v))
        exact (B19.commLeSub (commV L)).mul_mem hca
          ((B19.commLeSub (commV L)).inv_mem (hle (Subgroup.mem_sup_right ha)))
    rw [hle2] at hd
    have h1 : c * a * c⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.1 hd
    have h2 := congrArg (fun y => y * a * c) h1
    simpa [mul_assoc] using h2
  intro x hx
  have hLA : L ⊔ A ≤ Subgroup.centralizer ({c} : Set (MulAut V)) := sup_le hLc hAc
  exact Subgroup.mem_centralizer_iff.1 (hLA hx) c rfl

omit [Finite V] in
theorem s5_sq_mem {L A : Subgroup (MulAut V)} (hLq : CFSG.IsQuasisimple ↥L)
    (hn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (e : ↥(L ⊔ A) ≃* Equiv.Perm (Fin 5)) :
    ∀ y ∈ L ⊔ A, y ^ 2 ∈ L := by
  have hLn : (L.subgroupOf (L ⊔ A)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 ?_
    refine sup_le (fun l hl => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl),
        fun hx => by
          have := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
          simpa [mul_assoc] using this⟩
    · exact Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hn a ha x hx, fun hx => by
        have := hn a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
        simpa [mul_assoc] using this⟩
  set L' := L.subgroupOf (L ⊔ A) with hL'
  have eL : ↥L ≃* ↥L' := (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm
  have hq' : CFSG.IsQuasisimple ↥L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hLq
  let P : Subgroup (Equiv.Perm (Fin 5)) := L'.map e.toMonoidHom
  have hPn : P.Normal := Subgroup.Normal.map hLn e.toMonoidHom e.surjective
  have eP : ↥L' ≃* ↥P := L'.equivMapOfInjective e.toMonoidHom e.injective
  have hqP : CFSG.IsQuasisimple ↥P := CFSG.LocalCores.isQuasisimple_of_mulEquiv eP hq'
  have : Group.IsPerfect ↥P := hqP.1
  have : Nontrivial ↥P := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open hqP)
  obtain ⟨-, hPA⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternating.symmetric_perfect_subnormal P
      hPn.isSubnormal
  intro y hy
  have hsq : e ⟨y, hy⟩ ^ 2 ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_pow]
    simp
  rw [← hPA] at hsq
  obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.1 hsq
  have hz' : z = (⟨y, hy⟩ : ↥(L ⊔ A)) ^ 2 := e.injective (by rw [map_pow]; exact hze)
  rw [hz'] at hz
  exact hz

theorem case2_false
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection) (hI : B58Inputs)
    {G : Subgroup (MulAut V)} (hc : B56Counterex G) {A L : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) (hL : CFSG.Open.IsComponentOf L G) (hOff : B510Offenders G (L ⊔ A))
    (h : B59Case2 A L) : False := by
  have hJ : G = ffJ G := hc.hyp.2.1
  have hn' := B55.normalizes_comp hP4 hc.hV hJ hL
  have hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun b hb l hl =>
    B19Aux.conj_mem_of_le_normalizer hn' hb hl
  have hLq : CFSG.IsQuasisimple ↥L := B1Red.isQuasisimple_of_open hL.2.2
  have hAG : A ≤ G := hA.1.1
  have hLAG : L ⊔ A ≤ G := sup_le hL.1 hAG
  obtain ⟨hcomm, hdec, -⟩ := dich_case2 h
  obtain ⟨hiso, -, hsym, -⟩ := h
  obtain ⟨π, hπ⟩ := hsym
  have hfaith' : ∀ x ∈ L ⊔ A, (∀ w ∈ commV L, x w = w) → x = 1 :=
    faithful_on_of_realizes (symDn_faithful (by norm_num)) hπ
  have hfaith : ∀ x ∈ L ⊔ A, (∀ w ∈ commV (L ⊔ A), x w = w) → x = 1 := by
    rw [hcomm]
    exact hfaith'
  have hle : L ⊔ A ≤ B19.commLeSub (commV L) := B19.commV_le_iff.1 (le_of_eq hcomm)
  have hcent' := centralizes_case2 hc.hV hc.hyp.1 hAG hn hle
    (fun x hx hxw => hfaith' x ((le_sup_left : L ≤ L ⊔ A) hx) hxw)
  have hcent : ∀ c ∈ G, (∀ w ∈ commV (L ⊔ A), c w = w) → ∀ x ∈ L ⊔ A, c * x = x * c := by
    rw [hcomm]
    exact hcent'
  have hdata := b510_two hJ hLAG hfaith hcent hOff
  have hs := hdata.toSplit hdec
  have hsym' : SymmetricNatural (L ⊔ A) (commV L) ⊥ 5 := ⟨π, hπ⟩
  have hnA : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L := fun a ha l hl => hn a (hAG ha) l hl
  exact finish_nonexc hI hc hs (fun hbot => nontrivial_of_component hL (by
      rw [eq_bot_iff] at hbot ⊢
      exact (le_sup_left : L ≤ L ⊔ A).trans hbot))
    (piece_case2 hs hcomm hiso hsym')
    fun h2 => b56Case1_of_split hB51 hA21 hc hL.1 hn hLq (fun y hy => by
      rw [eq_of_bot hdata h2] at hy
      exact s5_sq_mem hLq hnA hiso.some y hy) (b56List_s5 hLq hnA hiso.some)

end Asm

theorem asB5610_of_inputs
    (hP4 : AsB15Part4) (hB51 : AsB51) (hA21 : AsA21SQTKSection)
    (hOff : B510OffendersAll) (hTail : B512Tail) : AsB5610 := by
  intro V _ _ G hc A L hA hL hLA hcase
  have hO := hOff V G hc A L hA hL hLA hcase
  rcases hcase with c1 | c2 | c3 | c4 | c5
  · exact case1_false hP4 hB51 hA21 b58Inputs hc hL (hO.1 (Or.inl c1)) c1
  · exact case2_false hP4 hB51 hA21 b58Inputs hc hA hL (hO.2 c2) c2
  · exact case3_false hP4 hB51 hA21 b58Inputs hc hA hL (hO.1 (Or.inr (Or.inl c3))) c3
  · exact case4_false hP4 hB51 hA21 b58Inputs hTail hc hL (hO.1 (Or.inr (Or.inr (Or.inl c4)))) c4
  · exact case5_false hP4 hB51 hA21 b58Inputs hc hA hL (hO.1 (Or.inr (Or.inr (Or.inr c5)))) c5

end FFC

end CFSG.Quasithin
