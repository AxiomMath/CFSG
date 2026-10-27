module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Stmts
public import CFSG.Quasithin.Vol2.Ch11SecA13Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.Quasithin.Vol2.Ch11SecA13Line2
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA
open scoped IsMulCommutative commutatorElement

section Decomp

variable {W : Type*} [CommGroup W]

omit [CommGroup W] in
theorem commS_stable [Group W] {S : Subgroup (MulAut W)} {U : Subgroup W} (hSU : S ≤ stabW U)
    {s : MulAut W} (hs : s ∈ S) {a : W} (ha : a ∈ commS S U) : s a ∈ commS S U := by
  change a ∈ Subgroup.closure {w | ∃ t ∈ S, ∃ u ∈ U, t u * u⁻¹ = w} at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, u, hu, rfl⟩ := hx
    have e : (s * t * s⁻¹) (s u) * (s u)⁻¹ = s (t u * u⁻¹) := by simp
    exact e ▸ Subgroup.subset_closure ⟨s * t * s⁻¹, S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs),
      s u, (mem_stabW.mp (hSU hs) u).mp hu, rfl⟩
  | one => simp
  | mul x y _ _ hx hy => simpa using (commS S U).mul_mem hx hy
  | inv x _ hx => simpa using (commS S U).inv_mem hx

theorem decomp_eq_of_mul_eq {A Z : Subgroup W} (hAZ : A ⊓ Z = ⊥) {a a' z z' : W} (ha : a ∈ A)
    (ha' : a' ∈ A) (hz : z ∈ Z) (hz' : z' ∈ Z) (h : a * z = a' * z') : a = a' ∧ z = z' := by
  have e : a'⁻¹ * a = z' * z⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * z) * z⁻¹ := by group
      _ = a'⁻¹ * (a' * z') * z⁻¹ := by rw [h]
      _ = z' * z⁻¹ := by group
  have h1 : a'⁻¹ * a ∈ A ⊓ Z :=
    ⟨A.mul_mem (A.inv_mem ha') ha, e ▸ Z.mul_mem hz' (Z.inv_mem hz)⟩
  rw [hAZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  subst h1
  exact ⟨rfl, mul_left_cancel h⟩

noncomputable def extId (A Z : Subgroup W) (f : W → W) (w : W) : W := by
  classical
  exact if hw : ∃ p : W × W, p.1 ∈ A ∧ p.2 ∈ Z ∧ p.1 * p.2 = w then
    f (Classical.choose hw).1 * (Classical.choose hw).2 else w

theorem extId_mul {A Z : Subgroup W} (hAZ : A ⊓ Z = ⊥) (f : W → W) {a z : W} (ha : a ∈ A)
    (hz : z ∈ Z) : extId A Z f (a * z) = f a * z := by
  have hw : ∃ p : W × W, p.1 ∈ A ∧ p.2 ∈ Z ∧ p.1 * p.2 = a * z := ⟨(a, z), ha, hz, rfl⟩
  unfold extId
  rw [dite_eq_left hw]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec hw
  obtain ⟨e1, e2⟩ := decomp_eq_of_mul_eq hAZ h1 ha h2 hz h3
  rw [e1, e2]

theorem extId_of_mem {A Z : Subgroup W} (hAZ : A ⊓ Z = ⊥) (f : W → W) {a : W} (ha : a ∈ A) :
    extId A Z f a = f a := by
  have := extId_mul hAZ f ha Z.one_mem
  rwa [mul_one, mul_one] at this

theorem commute_of_ext {S : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hd : U = commS S U ⊔ Z) (hAZ : commS S U ⊓ Z = ⊥) (hSZ : ∀ s ∈ S, ∀ z ∈ Z, s z = z)
    (hSU : S ≤ stabW U)
    (he : ∀ φ ψ : W → W, (∀ u ∈ U, φ u ∈ U) → (∀ u ∈ U, ψ u ∈ U) →
      (∀ u ∈ U, ∀ v ∈ U, φ (u * v) = φ u * φ v) → (∀ u ∈ U, ∀ v ∈ U, ψ (u * v) = ψ u * ψ v) →
      (∀ s ∈ S, ∀ u ∈ U, φ (s u) = s (φ u)) → (∀ s ∈ S, ∀ u ∈ U, ψ (s u) = s (ψ u)) →
      ∀ y ∈ commS S U, φ (ψ y) = ψ (φ y))
    (f g : W → W) (hf : ∀ a ∈ commS S U, f a ∈ commS S U)
    (hg : ∀ a ∈ commS S U, g a ∈ commS S U)
    (hfm : ∀ a ∈ commS S U, ∀ b ∈ commS S U, f (a * b) = f a * f b)
    (hgm : ∀ a ∈ commS S U, ∀ b ∈ commS S U, g (a * b) = g a * g b)
    (hfs : ∀ s ∈ S, ∀ a ∈ commS S U, f (s a) = s (f a))
    (hgs : ∀ s ∈ S, ∀ a ∈ commS S U, g (s a) = s (g a)) :
    ∀ a ∈ commS S U, f (g a) = g (f a) := by
  set A := commS S U with hAdef
  have hdec : ∀ u ∈ U, ∃ a ∈ A, ∃ z ∈ Z, a * z = u := fun u hu => by
    rw [hd] at hu
    exact Subgroup.mem_sup.mp hu
  have hAU : A ≤ U := by rw [hd]; exact le_sup_left
  have hZU : Z ≤ U := by rw [hd]; exact le_sup_right
  have hext : ∀ k : W → W, (∀ a ∈ A, k a ∈ A) → (∀ a ∈ A, ∀ b ∈ A, k (a * b) = k a * k b) →
      (∀ s ∈ S, ∀ a ∈ A, k (s a) = s (k a)) →
      (∀ u ∈ U, extId A Z k u ∈ U) ∧
      (∀ u ∈ U, ∀ v ∈ U, extId A Z k (u * v) = extId A Z k u * extId A Z k v) ∧
      (∀ s ∈ S, ∀ u ∈ U, extId A Z k (s u) = s (extId A Z k u)) := by
    intro k hk hkm hks
    refine ⟨fun u hu => ?_, fun u hu v hv => ?_, fun s hs u hu => ?_⟩
    · obtain ⟨a, ha, z, hz, rfl⟩ := hdec u hu
      rw [extId_mul hAZ k ha hz]
      exact U.mul_mem (hAU (hk a ha)) (hZU hz)
    · obtain ⟨a, ha, z, hz, rfl⟩ := hdec u hu
      obtain ⟨b, hb, y, hy, rfl⟩ := hdec v hv
      have e : a * z * (b * y) = a * b * (z * y) := mul_mul_mul_comm _ _ _ _
      rw [e, extId_mul hAZ k (A.mul_mem ha hb) (Z.mul_mem hz hy), extId_mul hAZ k ha hz,
        extId_mul hAZ k hb hy, hkm a ha b hb]
      exact mul_mul_mul_comm _ _ _ _
    · obtain ⟨a, ha, z, hz, rfl⟩ := hdec u hu
      have hsa : s a ∈ A := commS_stable hSU hs ha
      rw [map_mul, hSZ s hs z hz, extId_mul hAZ k hsa hz, extId_mul hAZ k ha hz, map_mul,
        hSZ s hs z hz, hks s hs a ha]
  obtain ⟨f1, f2, f3⟩ := hext f hf hfm hfs
  obtain ⟨g1, g2, g3⟩ := hext g hg hgm hgs
  intro a ha
  have h := he _ _ f1 g1 f2 g2 f3 g3 a ha
  rwa [extId_of_mem hAZ g ha, extId_of_mem hAZ f (hg a ha), extId_of_mem hAZ f ha,
    extId_of_mem hAZ g (hf a ha)] at h

end Decomp

variable {G : Type} [Group G]

theorem map_commS_autOn {V U K : Subgroup G} (hUV : U ≤ V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    (commS (autOn K V) (U.subgroupOf V)).map V.subtype = ⁅U, K⁆ := by
  rw [commS, MonoidHom.map_closure, Subgroup.commutator_comm, Subgroup.commutator_def]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨s, hs, u, hu, rfl⟩, rfl⟩
    obtain ⟨k, hk, hkV, rfl⟩ := SecA.mem_autOn_iff.mp hs
    refine ⟨k, hk, u, Subgroup.mem_subgroupOf.mp hu, ?_⟩
    simp [conjV_apply_coe, commutatorElement_def]
  · rintro ⟨k, hk, u, hu, rfl⟩
    refine ⟨_, ⟨conjV V k (hKV hk), conjV_mem_autOn hk (hKV hk), ⟨u, hUV hu⟩,
      Subgroup.mem_subgroupOf.mpr hu, rfl⟩, ?_⟩
    simp [conjV_apply_coe, commutatorElement_def]

theorem mem_normalizer_comm_of [Finite G] {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_map_le ?_
  rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer hH, map_conj_eq_of_mem_normalizer hK]

theorem not_le_centralizer_commutator {U P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (h : ¬ P ≤ Subgroup.centralizer (U : Set G)) :
    ¬ P ≤ Subgroup.centralizer ((⁅U, P⁆ : Subgroup G) : Set G) := by
  intro hle
  apply h
  have h1 : ⁅⁅U, P⁆, P⁆ = ⊥ := by
    rw [Subgroup.commutator_comm ⁅U, P⁆ P]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  have h2 : ⁅⁅P, U⁆, P⁆ = ⊥ := by rw [Subgroup.commutator_comm P U]; exact h1
  have h3 : ⁅⁅P, P⁆, U⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [hP] at h3
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

noncomputable abbrev sTwoV (T L I V₂ : Subgroup G) : Subgroup (MulAut ↥(fsuV T I)) :=
  perfectCore (autOn L (fsuV T I) ⊓ stabW (V₂.subgroupOf (fsuV T I)))

theorem siegel_inf (hS : FactSiegelG2) (hG2o : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hG2 : KindG2 L (fsuV T I) n) {V₂ : Subgroup G}
    (hV₂ : IsVi T L I n 2 V₂) :
    commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)) ⊓
      (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hZ := autOn_fix_centralizer L (fsuV T I)
  have f₂ := isFlagW_of_isVi h hV₂
  obtain ⟨_, -, -, -, hc⟩ := h1102 G T L I n h
  rcases hc with ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨-, -, -, -, -, hG2'⟩
  · exact (kind_not_SL3_G2 hG2o h.one_lt ⟨K, inferInstance, inferInstance, hK, he⟩ hG2).elim
  · exact (kind_not_Sp4_G2 hG2o h.one_lt ⟨K, inferInstance, inferInstance, hK, he⟩ hG2).elim
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2'
    exact hS K n h.one_lt hK _ hsq _ _ π hπ hZ (commV_autOn_eq_top h) _ (isSylowTwoOf_P h) _ f₂

theorem mem_commS_iff (h : Hyp11 G T L I n) {V₂ : Subgroup G} (hV₂V : V₂ ≤ fsuV T I)
    (y : ↥(fsuV T I)) :
    y ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)) ↔ (y : G) ∈ ⁅V₂, LOf L V₂⁆ := by
  rw [sTwoV, perfectCore_eq_autOn_lOf h hV₂V, ← map_commS_autOn hV₂V (lOf_le_normalizer_fsuV h V₂)]
  exact (Subgroup.mem_map_iff_mem (fsuV T I).subtype_injective).symm

theorem commutator_sup_centralizer_eq (hL3 : FactLineSL3) (hLp : FactLineSp4) (hLg : FactLineG2)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) :
    ⁅V₂, LOf L V₂⁆ ⊔ (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) = V₂ := by
  have hV₂V := IsVi.le_fsuV hV₂
  have hd := congrArg (fun U => U.map (fsuV T I).subtype)
    (lineFacts hL3 hLp hLg h1102 h hV₂).2.2.2.1
  rw [Subgroup.map_sup, perfectCore_eq_autOn_lOf h hV₂V,
    map_commS_autOn hV₂V (lOf_le_normalizer_fsuV h V₂), Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hV₂V, inf_comm] at hd
  exact hd.symm

theorem le_normalizer_commutator_lOf {X : Subgroup G} (hXL : X ≤ Subgroup.normalizer (L : Set G))
    {V₂ : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V₂ : Set G)) :
    X ≤ Subgroup.normalizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G) := fun _x hx =>
  mem_normalizer_comm_of (hXV hx) (le_normalizer_lOf hXL hXV hx)

theorem isCComponent_commutator (hE : SecA.C11P9B.Stmt11_1_2RadU) (hL3 : FactLineSL3)
    (hLp : FactLineSp4) (hLg : FactLineG2) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {V₂ : Subgroup G} (hV₂ : IsVi T L I n 2 V₂) :
    quasithinIsCComponent (LOf L V₂)
      (Subgroup.normalizer ((⁅V₂, LOf L V₂⁆ : Subgroup G) : Set G)) :=
  (hE G T L I n V₂ _ h hV₂ (commutator_sup_centralizer_eq hL3 hLp hLg h1102 h hV₂)
    (le_normalizer_commutator_lOf h.normal (IsVi.le_normalizer hV₂))
    (le_normalizer_commutator_lOf (inf_le_left.trans Subgroup.le_normalizer) inf_le_right)).1

theorem rad11_1_3_of (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (hG2o : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (hL3 : FactLineSL3) (hLp : FactLineSp4)
    (hLg : FactLineG2) (hS : FactSiegelG2) (hE : SecA.C11P9B.Stmt11_1_2RadU) : Rad11_1_3 := by
  intro G _ _ T L I n V₂ h hG2 _ hV₂
  have hV₂V := IsVi.le_fsuV hV₂
  set A₂ := ⁅V₂, LOf L V₂⁆ with hA₂def
  have hL₂N : LOf L V₂ ≤ Subgroup.normalizer (V₂ : Set G) :=
    (perfectCore_le _).trans inf_le_right
  have hA₂V₂ : A₂ ≤ V₂ := by
    rw [hA₂def, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hL₂N
  have hA₂V : A₂ ≤ fsuV T I := hA₂V₂.trans hV₂V
  have hCc := isCComponent_commutator hE hL3 hLp hLg h1102 h hV₂
  have hnc : ¬ LOf L V₂ ≤ Subgroup.centralizer (A₂ : Set G) :=
    not_le_centralizer_commutator hCc.2.1 (not_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂)
  refine ⟨hCc, hnc, fun K hK hKC => ?_⟩
  by_contra hne
  have hA₂1 : A₂ ≠ ⊥ := by
    intro hb
    apply hnc
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hb, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
    rw [hy, one_mul, mul_one]
  have hH : pCoreOf 2 (Subgroup.normalizer (A₂ : Set G)) ≠ ⊥ := by
    have hp : IsPGroup 2 ↥A₂ := (isPGroup_fsuV h).to_le hA₂V
    have hle : A₂ ≤ pCoreOf 2 (Subgroup.normalizer (A₂ : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hp
    intro hb
    rw [hb] at hle
    exact hA₂1 (le_bot_iff.mp hle)
  have := h.fsu.simple
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  have hKL₂ : ⁅K, LOf L V₂⁆ ≤ pCoreOf 2 (LOf L V₂) :=
    (QuasithinUnique.Vol2Native.lemma_1_2_1_two hloc h37 hH hK hCc hne).1.trans inf_le_right
  have hO₂ : pCoreOf 2 (LOf L V₂) ≤ Subgroup.centralizer (A₂ : Set G) :=
    (pCoreOf_lOf_le_centralizer hL3 hLp hLg h1102 h hV₂).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hA₂V₂))
  have hKN : K ≤ Subgroup.normalizer (A₂ : Set G) := le_of_mem_cComp hK
  have hL₂A : LOf L V₂ ≤ Subgroup.normalizer (A₂ : Set G) := le_of_mem_cComp hCc
  have hcomm : ∀ k ∈ K, ∀ l ∈ LOf L V₂, ∀ a ∈ A₂,
      k * (l * a * l⁻¹) * k⁻¹ = l * (k * a * k⁻¹) * l⁻¹ := by
    intro k hk l hl a ha
    have hc : ⁅k, l⁆ ∈ Subgroup.centralizer (A₂ : Set G) :=
      hO₂ (hKL₂ (Subgroup.commutator_mem_commutator hk hl))
    have hka : k * a * k⁻¹ ∈ A₂ := (Subgroup.mem_normalizer_iff.mp (hKN hk) a).mp ha
    have hlka : l * (k * a * k⁻¹) * l⁻¹ ∈ A₂ :=
      (Subgroup.mem_normalizer_iff.mp (hL₂A hl) _).mp hka
    have hc' := Subgroup.mem_centralizer_iff.mp hc _ hlka
    rw [commutatorElement_def] at hc'
    calc k * (l * a * l⁻¹) * k⁻¹
        = (k * l * k⁻¹ * l⁻¹) * (l * (k * a * k⁻¹) * l⁻¹) * (k * l * k⁻¹ * l⁻¹)⁻¹ := by group
      _ = l * (k * a * k⁻¹) * l⁻¹ := by rw [← hc']; group
  obtain ⟨_, -, -, -, -⟩ := h1102 G T L I n h
  have hLF := lineFacts hL3 hLp hLg h1102 h hV₂
  have hAZ := siegel_inf hS hG2o h1102 h hG2 hV₂
  have hSZ : ∀ s ∈ sTwoV T L I V₂, ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I),
      s z = z := fun s hs =>
    autOn_fix_centralizer L (fsuV T I) s (((perfectCore_le _).trans inf_le_left) hs)
  have hSU : sTwoV T L I V₂ ≤ stabW (V₂.subgroupOf (fsuV T I)) :=
    (perfectCore_le _).trans inf_le_right
  have hmem := mem_commS_iff h hV₂V
  have hmaps : ∀ k (hk : k ∈ K),
      (∀ a ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)),
        conjOn (fsuV T I) A₂ hA₂V k (hKN hk) a ∈
          commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I))) ∧
      (∀ a ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)),
        ∀ b ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)),
        conjOn (fsuV T I) A₂ hA₂V k (hKN hk) (a * b) =
          conjOn (fsuV T I) A₂ hA₂V k (hKN hk) a * conjOn (fsuV T I) A₂ hA₂V k (hKN hk) b) ∧
      (∀ s ∈ sTwoV T L I V₂, ∀ a ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)),
        conjOn (fsuV T I) A₂ hA₂V k (hKN hk) (s a) =
          s (conjOn (fsuV T I) A₂ hA₂V k (hKN hk) a)) := by
    intro k hk
    have hkN := hKN hk
    refine ⟨fun a ha => ?_, fun a ha b hb => ?_, fun s hs a ha => ?_⟩
    · have ha' := (hmem a).mp ha
      rw [hmem, conjOn_coe hA₂V _ ha']
      exact (Subgroup.mem_normalizer_iff.mp hkN _).mp ha'
    · have ha' := (hmem a).mp ha
      have hb' := (hmem b).mp hb
      apply Subtype.ext
      have hab : ((a * b : ↥(fsuV T I)) : G) ∈ A₂ := A₂.mul_mem ha' hb'
      rw [conjOn_coe hA₂V _ hab, Subgroup.coe_mul, Subgroup.coe_mul, conjOn_coe hA₂V _ ha',
        conjOn_coe hA₂V _ hb']
      group
    · have hs' := hs
      rw [sTwoV, perfectCore_eq_autOn_lOf h hV₂V] at hs'
      obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hs'
      have ha' := (hmem a).mp ha
      have hsa : ((conjV (fsuV T I) l hlV a : ↥(fsuV T I)) : G) ∈ A₂ := by
        rw [conjV_apply_coe]
        exact (Subgroup.mem_normalizer_iff.mp (hL₂A hl) _).mp ha'
      apply Subtype.ext
      rw [conjOn_coe hA₂V _ hsa, conjV_apply_coe, conjV_apply_coe, conjOn_coe hA₂V _ ha']
      exact hcomm k hk l hl a ha'
  have hcK : ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ a ∈ A₂,
      k₁ * (k₂ * a * k₂⁻¹) * k₁⁻¹ = k₂ * (k₁ * a * k₁⁻¹) * k₂⁻¹ := by
    intro k₁ hk₁ k₂ hk₂ a ha
    obtain ⟨m₁, a₁, c₁⟩ := hmaps k₁ hk₁
    obtain ⟨m₂, a₂, c₂⟩ := hmaps k₂ hk₂
    have haA : (⟨a, hA₂V ha⟩ : ↥(fsuV T I)) ∈ commS (sTwoV T L I V₂) (V₂.subgroupOf (fsuV T I)) :=
      (hmem _).mpr ha
    have e := congrArg Subtype.val (commute_of_ext hLF.2.2.2.1 hAZ hSZ hSU hLF.2.2.2.2 _ _ m₁ m₂
      a₁ a₂ c₁ c₂ _ haA)
    have hy₁ := (hmem _).mp (m₁ _ haA)
    have hy₂ := (hmem _).mp (m₂ _ haA)
    rw [conjOn_coe hA₂V _ hy₂, conjOn_coe hA₂V _ hy₁, conjOn_coe hA₂V _ ha,
      conjOn_coe hA₂V _ ha] at e
    exact e
  apply hKC
  have hD : ⁅K, K⁆ ≤ Subgroup.centralizer (A₂ : Set G) := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hcK k₁⁻¹ (K.inv_mem hk₁) k₂⁻¹ (K.inv_mem hk₂) a ha
    simp only [inv_inv] at this
    rw [commutatorElement_def]
    calc a * (k₁ * k₂ * k₁⁻¹ * k₂⁻¹)
        = k₁ * k₂ * (k₂⁻¹ * k₁⁻¹ * a * k₁ * k₂) * k₁⁻¹ * k₂⁻¹ := by group
      _ = k₁ * k₂ * (k₁⁻¹ * k₂⁻¹ * a * k₂ * k₁) * k₁⁻¹ * k₂⁻¹ := by
          congr 3
          calc k₂⁻¹ * k₁⁻¹ * a * k₁ * k₂ = k₂⁻¹ * (k₁⁻¹ * a * k₁) * k₂ := by group
            _ = k₁⁻¹ * (k₂⁻¹ * a * k₂) * k₁ := this.symm
            _ = k₁⁻¹ * k₂⁻¹ * a * k₂ * k₁ := by group
      _ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ * a := by group
  exact hK.2.1.symm.le.trans hD

end CFSG.Quasithin.Vol2.Ch11.G2Q8
