module

public import CFSG.Quasithin.EmptyFaithful.SBdK36Gen
public import CFSG.Quasithin.EmptyFaithful.ModHBr

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

variable {G : Type} [Group G] {I : Subgroup G} {Q : Type} [Group Q]

@[expose] def img (ρ : ↥I →* Q) (A : Subgroup G) : Subgroup Q := (A.subgroupOf I).map ρ

theorem mem_img {ρ : ↥I →* Q} {A : Subgroup G} {q : Q} :
    q ∈ img ρ A ↔ ∃ (a : G) (ha : a ∈ I), a ∈ A ∧ ρ ⟨a, ha⟩ = q := by
  simp only [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, x.2, hx, rfl⟩
  · rintro ⟨a, ha, hA, rfl⟩
    exact ⟨⟨a, ha⟩, hA, rfl⟩

theorem img_mono {ρ : ↥I →* Q} {A B : Subgroup G} (h : A ≤ B) : img ρ A ≤ img ρ B := by
  intro q hq
  obtain ⟨a, ha, hA, rfl⟩ := mem_img.1 hq
  exact mem_img.2 ⟨a, ha, h hA, rfl⟩

theorem img_sup {ρ : ↥I →* Q} {A B : Subgroup G} (hA : A ≤ I) (hB : B ≤ I) :
    img ρ (A ⊔ B) = img ρ A ⊔ img ρ B := by
  simp only [img]
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem isSylowTwoOf_of_le_top {P P' : Subgroup Q} (hP : IsSylowTwoOf P ⊤) (hle : P ≤ P')
    (hp : IsPGroup 2 ↥P') : IsSylowTwoOf P' ⊤ := by
  obtain ⟨-, hi⟩ := K1.isSylowTwoOf_top_iff.mp hP
  exact K1.isSylowTwoOf_top_iff.mpr ⟨hp, fun h2 => hi (h2.trans (Subgroup.index_dvd_of_le hle))⟩

section Ctx

variable [Finite G] {T Mc M V₁ V₂ Yp L : Subgroup G} {t : G}

theorem quotSylow_of_ctx (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) :
    IsSylowTwoOf (((Sgp153 T V₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨Tsyl, hT, -, -⟩ := R3c10.exists_quotSylow hZ hQsyl
  rw [← hT]
  exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩

omit [Finite G] in
theorem rho_surjective (hLI : L ≤ I) (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L)
    (hρ : ∀ l : ↥L, ρ ⟨l, hLI l.2⟩ = QuotientGroup.mk l) : Function.Surjective ρ := by
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨⟨l, hLI l.2⟩, hρ l⟩

theorem isSylowTwoOf_img_S (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hLI : L ≤ I) (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L)
    (hρ : ∀ l : ↥L, ρ ⟨l, hLI l.2⟩ = QuotientGroup.mk l) :
    IsSylowTwoOf (img ρ (Sgp153 T V₁)) ⊤ := by
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hS2 : IsPGroup 2 ↥(Sgp153 T V₁) := c.facts.sylow.2.1
  have hP2 : IsPGroup 2 ↥(img ρ (Sgp153 T V₁)) := by
    have h1 : IsPGroup 2 ↥((Sgp153 T V₁).subgroupOf I) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSI).symm
    exact h1.of_surjective (ρ.subgroupMap ((Sgp153 T V₁).subgroupOf I))
      (ρ.subgroupMap_surjective _)
  refine isSylowTwoOf_of_le_top (quotSylow_of_ctx c hN) ?_ hP2
  intro q hq
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hq
  refine mem_img.2 ⟨l, hLI l.2, (Subgroup.mem_subgroupOf.1 hl).1, ?_⟩
  rw [hρ l]
  rfl

omit [Finite G] in
theorem img_le_normalizer_img {A B : Subgroup G} {ρ : ↥I →* Q}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    img ρ A ≤ Subgroup.normalizer ((img ρ B : Subgroup Q) : Set Q) := by
  have key : ∀ (a : G) (ha : a ∈ I), a ∈ A → ∀ x ∈ img ρ B,
      ρ ⟨a, ha⟩ * x * (ρ ⟨a, ha⟩)⁻¹ ∈ img ρ B := by
    intro a ha haA x hx
    obtain ⟨b, hb, hbB, rfl⟩ := mem_img.1 hx
    have hab : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 (h haA) b).1 hbB
    refine mem_img.2 ⟨a * b * a⁻¹, I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha), hab, ?_⟩
    have : (⟨a * b * a⁻¹, I.mul_mem (I.mul_mem ha hb) (I.inv_mem ha)⟩ : ↥I) =
        ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  intro g hg
  obtain ⟨a, ha, haA, rfl⟩ := mem_img.1 hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key a ha haA x
  · intro hx
    have h1 := key a⁻¹ (I.inv_mem ha) (A.inv_mem haA) _ hx
    have h2 : ρ ⟨a⁻¹, I.inv_mem ha⟩ = (ρ ⟨a, ha⟩)⁻¹ := by
      rw [← map_inv]; rfl
    rw [h2, inv_inv] at h1
    simpa [mul_assoc] using h1

theorem solvable_nine_img_Yp (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hLI : L ≤ I) (hYL : Yp ≤ L)
    (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L) (hker : IsPGroup 2 ρ.ker) :
    Group.IsSolvable ↥(img ρ Yp) ∧ 9 ∣ Nat.card ↥(img ρ Yp) := by
  have hYI : Yp ≤ I := hYL.trans hLI
  obtain ⟨b, k, hk2, -, hcard⟩ := SBd11.card_form_of_struct c.facts11.struct_Yp
  have hsolvY : Group.IsSolvable ↥Yp := isSolvable_of_struct c.facts11.struct_Yp
  let ψ : ↥Yp →* ↥L ⧸ Subgroup.center ↥L := ρ.comp (Subgroup.inclusion hYI)
  have hrange : ψ.range = img ρ Yp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_img.2 ⟨y.1, hYI y.2, y.2, rfl⟩
    · intro hx
      obtain ⟨a, ha, haY, rfl⟩ := mem_img.1 hx
      exact ⟨⟨a, haY⟩, rfl⟩
  have hK2 : IsPGroup 2 ψ.ker := by
    intro z
    obtain ⟨m, hm⟩ := hker ⟨Subgroup.inclusion hYI z.1, z.2⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun w : ↥ρ.ker => ((w : ↥I) : G)) hm
    simpa using this
  have hsolv : Group.IsSolvable ↥(img ρ Yp) := by
    rw [← hrange]
    exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hprod := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 hK2
  have h3k : 3 ^ k ∣ Nat.card ψ.range := by
    have h1 : 3 ^ k ∣ Nat.card ψ.ker * Nat.card ψ.range := by
      rw [hprod, hcard]
      exact Dvd.intro_left _ rfl
    have hcop : Nat.Coprime (3 ^ k) (Nat.card ψ.ker) := by
      rw [hi]
      exact Nat.Coprime.pow k i (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h1
  have h9 : 9 ∣ Nat.card ψ.range := (pow_dvd_pow 3 hk2).trans h3k
  exact ⟨hsolv, by rw [← hrange]; exact h9⟩

theorem hmin_prop (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hmin : ∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I)
    (hLI : L ≤ I) (hYL : Yp ≤ L) (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L)
    (hρ : ∀ l : ↥L, ρ ⟨l, hLI l.2⟩ = QuotientGroup.mk l) (hker : IsPGroup 2 ρ.ker)
    (N : Subgroup (↥L ⧸ Subgroup.center ↥L)) (hNp : IsPGroup 2 ↥N) (hN1 : N ≠ ⊥)
    (hZN : img ρ (Yp ⊔ Sgp153 T V₁) ≤ Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)))
    (hNtop : Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)) ≠ ⊤) :
    Subgroup.normalizer (N : Set (↥L ⧸ Subgroup.center ↥L)) ≤
      Subgroup.normalizer ((img ρ Yp : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
        Set (↥L ⧸ Subgroup.center ↥L)) := by
  have hYI : Yp ≤ I := hYL.trans hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hsurj := rho_surjective hLI ρ hρ
  set NN : Subgroup (↥L ⧸ Subgroup.center ↥L) := Subgroup.normalizer (N : Set _) with hNN
  set Nt : Subgroup ↥I := N.comap ρ with hNt
  set W : Subgroup ↥I := NN.comap ρ with hW
  set Wg : Subgroup G := W.map I.subtype with hWg
  have memWg : ∀ g : G, g ∈ Wg ↔ ∃ hg : g ∈ I, ρ ⟨g, hg⟩ ∈ NN := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, hgn⟩
      exact ⟨⟨g, hg⟩, hgn, rfl⟩
  have hWgI : Wg ≤ I := by
    rintro g ⟨x, -, rfl⟩
    exact x.2
  have hYSW : Yp ⊔ Sgp153 T V₁ ≤ Wg := by
    refine sup_le (fun y hy => ?_) (fun s hs => ?_)
    · exact (memWg y).2 ⟨hYI hy, hZN (mem_img.2 ⟨y, hYI hy, Subgroup.mem_sup_left hy, rfl⟩)⟩
    · exact (memWg s).2 ⟨hSI hs, hZN (mem_img.2 ⟨s, hSI hs, Subgroup.mem_sup_right hs, rfl⟩)⟩
  set Ntg : Subgroup G := Nt.map I.subtype with hNtg
  have hNtW : Nt ≤ W := fun u hu => Subgroup.le_normalizer (show ρ u ∈ N from hu)
  have hNtgW : Ntg ≤ Wg := Subgroup.map_mono hNtW
  have hfwd : ∀ w ∈ W, ∀ u ∈ Nt, w * u * w⁻¹ ∈ Nt := by
    intro w hw u hu
    have hw' : ρ w ∈ NN := hw
    have hu' : ρ u ∈ N := hu
    show ρ (w * u * w⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hw' (ρ u)).1 hu'
  have hNtgnorm : Wg ≤ Subgroup.normalizer (Ntg : Set G) := by
    intro g hg
    obtain ⟨w, hw, rfl⟩ := hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨w * u * w⁻¹, hfwd w hw u hu, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨w⁻¹ * v * w, ?_, ?_⟩
      · have := hfwd w⁻¹ (W.inv_mem hw) v hv
        simpa using this
      · have h1 : I.subtype (w⁻¹ * v * w) = (I.subtype w)⁻¹ * I.subtype v * I.subtype w := by
          simp [map_mul, map_inv]
        rw [h1, hvx]
        group
  have hNtgp : IsPGroup 2 ↥Ntg := by
    intro g
    obtain ⟨u, hu, hug⟩ := g.2
    obtain ⟨a, ha⟩ := hNp ⟨ρ u, hu⟩
    have hua : u ^ (2 ^ a) ∈ ρ.ker := by
      show ρ (u ^ (2 ^ a)) = 1
      rw [map_pow]
      have := congrArg (fun z : ↥N => (z : ↥L ⧸ Subgroup.center ↥L)) ha
      simpa using this
    obtain ⟨m, hm⟩ := hker ⟨u ^ (2 ^ a), hua⟩
    refine ⟨a + m, Subtype.ext ?_⟩
    have h1 := congrArg (fun z : ↥ρ.ker => ((z : ↥I) : G)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    have h2 : ((g : ↥Ntg) : G) = (u : G) := hug.symm
    show ((g : G)) ^ (2 ^ (a + m)) = 1
    rw [h2, pow_add, pow_mul]
    simpa using h1
  have hNtgle : Ntg ≤ pCoreOf 2 Wg :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNtgW hNtgnorm hNtgp
  have hNtg1 : Ntg ≠ ⊥ := by
    obtain ⟨⟨n, hn⟩, hn1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hN1
    have hn1 : n ≠ 1 := fun h => hn1' (Subtype.ext h)
    obtain ⟨u, hu⟩ := hsurj n
    intro hbot
    have hu1 : u ∈ Nt := by
      show ρ u ∈ N
      rw [hu]
      exact hn
    have hmem : (u : G) ∈ Ntg := ⟨u, hu1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : u = 1 := Subtype.ext hmem
    apply hn1
    rw [← hu, this, map_one]
  have hpc : pCoreOf 2 Wg ≠ ⊥ := fun h => hNtg1 (le_bot_iff.1 (h ▸ hNtgle))
  intro q hq
  obtain ⟨i, rfl⟩ := hsurj q
  have hiW : (i : G) ∈ Wg := (memWg _).2 ⟨i.2, hq⟩
  by_cases hWM : Wg ≤ M
  · have hiM : (i : G) ∈ M ⊓ I := ⟨hWM hiW, i.2⟩
    have hiN : (i : G) ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [c.facts.norm_eq]; exact hiM
    have hz : Subgroup.zpowers (i : G) ≤ Subgroup.normalizer (Yp : Set G) :=
      Subgroup.zpowers_le.2 hiN.2
    exact img_le_normalizer_img hz (mem_img.2 ⟨i, i.2, Subgroup.mem_zpowers _, rfl⟩)
  · exfalso
    have hHP : IsHPlus Yp (Sgp153 T V₁) M Wg := ⟨⟨hYSW, hpc⟩, hWM⟩
    have hWI : Wg = I := hmin Wg hHP hWgI
    apply hNtop
    rw [eq_top_iff]
    intro q' _
    obtain ⟨i', rfl⟩ := hsurj q'
    have : (i' : G) ∈ Wg := by rw [hWI]; exact i'.2
    obtain ⟨hg, hgn⟩ := (memWg _).1 this
    exact hgn

theorem s3s3_img (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hLI : L ≤ I) (hYL : Yp ≤ L)
    (ρ : ↥I →* ↥L ⧸ Subgroup.center ↥L) (hker : IsPGroup 2 ρ.ker) :
    ∃ φ : ↥(img ρ (Yp ⊔ Sgp153 T V₁)) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3),
      Function.Surjective φ := by
  have hYI : Yp ≤ I := hYL.trans hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hHI : Yp ⊔ Sgp153 T V₁ ≤ I := sup_le hYI hSI
  obtain ⟨φ, hφs, hφk⟩ := c.s3s3
  let ρH : ↥(Yp ⊔ Sgp153 T V₁) →* ↥(img ρ (Yp ⊔ Sgp153 T V₁)) :=
    (ρ.comp (Subgroup.inclusion hHI)).codRestrict (img ρ (Yp ⊔ Sgp153 T V₁))
      (fun h => mem_img.2 ⟨h.1, hHI h.2, h.2, rfl⟩)
  have hρHs : Function.Surjective ρH := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha, haH, rfl⟩ := mem_img.1 hz
    exact ⟨⟨a, haH⟩, rfl⟩
  have hK2 : IsPGroup 2 ρH.ker := by
    intro z
    obtain ⟨m, hm⟩ := hker ⟨Subgroup.inclusion hHI z.1, by
      have := z.2
      rw [MonoidHom.mem_ker] at this ⊢
      exact congrArg Subtype.val this⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun w : ↥ρ.ker => ((w : ↥I) : G)) hm
    simpa using this
  have hkle : ρH.ker ≤ φ.ker := by
    intro h hh
    have hnorm : (ρH.ker).Normal := MonoidHom.normal_ker ρH
    have hcore : ρH.ker ≤ CFSG.Open.pCore 2 ↥(Yp ⊔ Sgp153 T V₁) :=
      CFSG.LieType.BorelTits.le_pCore 2 hnorm hK2
    have h1 : (h : G) ∈ pCoreOf 2 (Yp ⊔ Sgp153 T V₁) := ⟨h, hcore hh, rfl⟩
    rw [hφk, Subgroup.mem_subgroupOf]
    exact SBd.pCoreOf_le_oTwoPhi _ h1
  let φ' : ↥(img ρ (Yp ⊔ Sgp153 T V₁)) →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) :=
    MonoidHom.liftOfRightInverse ρH (Function.surjInv hρHs) (Function.rightInverse_surjInv hρHs)
      ⟨φ, hkle⟩
  refine ⟨φ', fun t' => ?_⟩
  obtain ⟨h, rfl⟩ := hφs t'
  exact ⟨ρH h, by
    simp [φ', MonoidHom.liftOfRightInverse_comp_apply]⟩

end Ctx

end CFSG.Quasithin.ModH
