module

public import CFSG.RankThree.PartOne.S12.Sec1510Y
public import CFSG.RankThree.PartOne.S12.Sec1510FiveDefs
public import CFSG.RankThree.PartOne.S12.Sec159Node
public import CFSG.RankThree.PartOne.S12.Sec159Tr
import CFSG.RankThree.PartOne.S12.Sec12A
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S12.Sec159Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec1510Node

variable {G : Type} [Group G]

omit [Group G] in
theorem theta_quotient_nilpotent_bot {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {M : Subgroup (H ⧸ aschbacherSolvableCore p H)} (hMn : M.Normal) (hnil : Group.IsNilpotent ↥M)
    (hMp : ¬ p ∣ Nat.card ↥M) : M = ⊥ := by
  obtain ⟨hθs, -, hθp, hmax, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set θ := aschbacherSolvableCore p H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set M' : Subgroup H := M.comap π with hM'
  have hM'n : M'.Normal := hMn.comap π
  have hθM' : θ ≤ M' := fun x hx => by
    rw [hM', Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
    exact M.one_mem
  have hMs : Group.IsSolvable ↥M := inferInstance
  have hsolv : Group.IsSolvable ↥M' := by
    let f : ↥θ →* ↥M' := Subgroup.inclusion hθM'
    let g : ↥M' →* ↥M := (π.comp M'.subtype).codRestrict M fun x => x.2
    refine Group.isSolvable_of_ker_le_range f g ?_
    intro x hx
    have h1 : π (x : H) = 1 := congrArg Subtype.val hx
    have h2 : (x : H) ∈ θ := (QuotientGroup.eq_one_iff (x : H)).1 h1
    exact ⟨⟨x, h2⟩, rfl⟩
  have hcard : Nat.card ↥M' = Nat.card ↥θ * Nat.card ↥M :=
    QuotientGroup.card_preimage_mk θ (M : Set (H ⧸ θ))
  have hndvd : ¬ p ∣ Nat.card ↥M' := by
    intro h
    rw [hcard] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · exact hθp h1
    · exact hMp h1
  have hle : M' ≤ θ := hmax M' hM'n hsolv hndvd
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hh : h ∈ M' := hq
  have := hle hh
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff h).2 this

omit [Group G] in
theorem mem_normalizer_of_subgroupOf {G : Type} [Group G] {X E : Subgroup G} (hE : E ≤ X) {n : ↥X}
    (hn : n ∈ Subgroup.normalizer ((E.subgroupOf X : Subgroup ↥X) : Set ↥X)) :
    (n : G) ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  by_cases hy : y ∈ X
  · have := Subgroup.mem_normalizer_iff.1 hn ⟨y, hy⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · have hy' : y ∉ E := fun h => hy (hE h)
    have hy'' : (n : G) * y * (n : G)⁻¹ ∉ E := by
      intro h
      apply hy
      have h1 := hE h
      have hn' : (n : G) ∈ X := n.2
      have := X.mul_mem (X.mul_mem (X.inv_mem hn') h1) hn'
      simpa [mul_assoc] using this
    exact ⟨fun h => absurd h hy', fun h => absurd h hy''⟩

omit [Group G] in
theorem le_normalizer_map_subtype {G : Type} [Group G] {X : Subgroup G} {N : Subgroup ↥X} [N.Normal] :
    X ≤ Subgroup.normalizer ((N.map X.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨g, hg⟩ * n * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem ‹N.Normal› n hn _, by simp⟩
  · rintro ⟨n, hn, hny⟩
    refine ⟨⟨g, hg⟩⁻¹ * n * ⟨g, hg⟩, by
      simpa using Subgroup.Normal.conj_mem ‹N.Normal› n hn ⟨g, hg⟩⁻¹, ?_⟩
    have : (n : G) = g * y * g⁻¹ := hny
    simp [this, mul_assoc]

omit [Group G] in
theorem layer_quotient_eq {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime) :
    (sSup (thetaComponents p H)).map (QuotientGroup.mk' (aschbacherSolvableCore p H)) =
      layer (H ⧸ aschbacherSolvableCore p H) := by
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) hp
  have himg := hbij.image_eq
  have h2 : (sSup (thetaComponents p H)).map (QuotientGroup.mk' (aschbacherSolvableCore p H)) =
      ⨆ L ∈ thetaComponents p H, L.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) :=
    (Subgroup.gc_map_comap _).l_sSup
  rw [h2]
  simp only [CFSG.layer.eq_sSup]
  rw [← himg, sSup_image]

theorem thetaLayer_eq {G : Type} [Group G] (p : ℕ) (e : G) :
    thetaLayer p e = (sSup (thetaComponents p ↥(Subgroup.centralizer ({e} : Set G)))).map
      (Subgroup.centralizer ({e} : Set G)).subtype := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨Y, ⟨L, hL, rfl⟩, ⟨x₀, hx₀, rfl⟩⟩
    exact ⟨x₀, le_sSup hL hx₀, rfl⟩
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL x hx => ?_
    exact Subgroup.subset_closure ⟨L.map (Subgroup.centralizer ({e} : Set G)).subtype,
      ⟨L, hL, rfl⟩, ⟨x, hx, rfl⟩⟩

theorem inn_transfer {C E : Subgroup G} {Lh : Subgroup ↥C} (hEC : E ≤ C)
    (hInn : ∀ x ∈ E, ∃ l ∈ E ⊓ Lh.map C.subtype,
      ∃ c' ∈ E ⊓ Subgroup.centralizer ((Lh.map C.subtype : Subgroup G) : Set G), x = l * c') :
    ∀ x ∈ E.subgroupOf C, ∃ l ∈ E.subgroupOf C ⊓ Lh,
      ∃ c' ∈ E.subgroupOf C ⊓ Subgroup.centralizer (Lh : Set ↥C), x = l * c' := by
  intro x hx
  obtain ⟨l, ⟨hlE, l₀, hl₀, hl₀l⟩, c', ⟨hcE, hcC⟩, hxlc⟩ :=
    hInn (x : G) (Subgroup.mem_subgroupOf.1 hx)
  have hl : (l₀ : G) = l := hl₀l
  refine ⟨l₀, ⟨Subgroup.mem_subgroupOf.2 (by rw [hl]; exact hlE), hl₀⟩, ⟨c', hEC hcE⟩,
    ⟨Subgroup.mem_subgroupOf.2 hcE, ?_⟩, Subtype.ext ?_⟩
  · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcC (z : G) ⟨z, hz, rfl⟩)
  · show (x : G) = (l₀ : G) * c'
    rw [hl]; exact hxlc

theorem omegaOne_subgroupOf {p : ℕ} {C E P : Subgroup G} (hEP : E ≤ P)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hPΩ : omegaOne p P = E) :
    omegaOne p (P.subgroupOf C) = E.subgroupOf C := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyP, hy1⟩
    have hyP' : (y : G) ∈ P := Subgroup.mem_subgroupOf.1 hyP
    have hy1' : (y : G) ^ p = 1 := by simpa using congrArg Subtype.val hy1
    have : (y : G) ∈ omegaOne p P := Subgroup.subset_closure ⟨hyP', hy1'⟩
    exact Subgroup.mem_subgroupOf.2 (hPΩ ▸ this)
  · intro y hy
    refine Subgroup.subset_closure ⟨Subgroup.mem_subgroupOf.2
      (hEP (Subgroup.mem_subgroupOf.1 hy)), ?_⟩
    exact Subtype.ext (hexp y (Subgroup.mem_subgroupOf.1 hy))

variable [Finite G]

theorem centralizer_le_gen {p : ℕ} (hp : p.Prime) {A E P N₀ : Subgroup G} {e : G}
    (hE : IsElementaryAbelian p ↥E) (hAE : A ≤ E) (hAel : IsElementaryAbelian p ↥A)
    (hAcard : Nat.card ↥A = p ^ 3)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hWN : Subgroup.normalizer (E : Set G) ≤ N₀)
    (hNA : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B → Subgroup.normalizer (B : Set G) ≤ N₀)
    (hND : ∀ D : Subgroup G,
      (∀ x : G, x ∈ D ↔ x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e) →
        ¬ IsCyclic ↥D → Subgroup.normalizer (D : Set G) ≤ N₀)
    (heE : e ∈ E) (he1 : e ≠ 1)
    (hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ N₀)
    (hInn : ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c')
    (hPsyl : IsSylowOf p P (Subgroup.centralizer ({e} : Set G))) (hEP : E ≤ P) (hPN : P ≤ N₀)
    (hPΩ : omegaOne p P = E) (hPc : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    Subgroup.centralizer ({e} : Set G) ≤ N₀ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) x hx
  set Ce : Subgroup G := Subgroup.centralizer ({e} : Set G) with hCe
  have hmemCe : ∀ x : G, x ∈ Ce ↔ x * e = e * x := fun x => Subgroup.mem_centralizer_singleton_iff
  have hEC : E ≤ Ce := fun x hx =>
    (hmemCe x).2 (congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨e, heE⟩))
  have heC : e ∈ Ce := hEC heE
  set θ : Subgroup ↥Ce := aschbacherSolvableCore p ↥Ce with hθ
  have hθn : θ.Normal := inferInstanceAs (aschbacherSolvableCore p ↥Ce).Normal
  set Lh : Subgroup ↥Ce := sSup (thetaComponents p ↥Ce) with hLh
  have hθp : ¬ p ∣ Nat.card ↥θ := (solvable_prime_complement_core_characterization (H := ↥Ce) hp).2.2.1
  have hLlayer : Lh.map (QuotientGroup.mk' θ) = layer (↥Ce ⧸ θ) := layer_quotient_eq hp
  have hVN : θ ≤ N₀.subgroupOf Ce := by
    have h1 : E ≤ Subgroup.normalizer
        ((inSubgroup (aschbacherSolvableCore p) Ce : Subgroup G) : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hEC.trans Subgroup.le_normalizer)
    have h2 : ¬ p ∣ Nat.card ↥(inSubgroup (aschbacherSolvableCore p) Ce) :=
      (theta_solvable_and_not_dvd hp Ce).2
    have h3 := Sec159.le_of_pPrime_normalized hp hAel hAcard hNA (fun a ha => h1 (hAE ha)) h2
    exact fun v hv => Subgroup.mem_subgroupOf.2 (h3 ⟨v, hv, rfl⟩)
  have hLhN : Lh ≤ N₀.subgroupOf Ce := by
    refine sSup_le fun Z hZ z hz => ?_
    exact Subgroup.mem_subgroupOf.2 (hLN (Z.map Ce.subtype) ⟨Z, hZ, rfl⟩ ⟨z, hz, rfl⟩)
  have hInn' : ∀ x ∈ E.subgroupOf Ce, ∃ l ∈ E.subgroupOf Ce ⊓ Lh,
      ∃ c' ∈ E.subgroupOf Ce ⊓ Subgroup.centralizer (Lh : Set ↥Ce), x = l * c' := by
    refine inn_transfer hEC ?_
    rw [← thetaLayer_eq p e] at *
    exact hInn
  set π : ↥Ce →* ↥Ce ⧸ θ := QuotientGroup.mk' θ with hπ
  set Dh : Subgroup ↥Ce := E.subgroupOf Ce ⊓ (Subgroup.centralizer
      ((Lh.map π : Subgroup (↥Ce ⧸ θ)) : Set (↥Ce ⧸ θ))).comap π with hDh
  have hDmem : ∀ x : G, x ∈ Dh.map Ce.subtype ↔
      x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e := by
    intro x
    constructor
    · rintro ⟨h, ⟨hhE, hhY⟩, rfl⟩
      refine ⟨Subgroup.mem_subgroupOf.1 hhE, ?_⟩
      intro l hl
      rw [thetaLayer_eq] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := hl
      have hc := Subgroup.mem_centralizer_iff.1 hhY (π l₀) ⟨l₀, hl₀, rfl⟩
      have h1 : π (h * l₀ * h⁻¹ * l₀⁻¹) = 1 := by
        have h2 : π h * π l₀ = π l₀ * π h := hc.symm
        calc π (h * l₀ * h⁻¹ * l₀⁻¹) = π h * π l₀ * (π h)⁻¹ * (π l₀)⁻¹ := by simp
          _ = π l₀ * π h * (π h)⁻¹ * (π l₀)⁻¹ := by rw [h2]
          _ = 1 := by group
      have h3 : h * l₀ * h⁻¹ * l₀⁻¹ ∈ θ := (QuotientGroup.eq_one_iff _).1 h1
      exact ⟨_, h3, by simp⟩
    · rintro ⟨hxE, hxl⟩
      have hxC : x ∈ Ce := (hmemCe x).2 (congrArg Subtype.val (hE.is_comm.comm ⟨x, hxE⟩ ⟨e, heE⟩))
      refine ⟨⟨x, hxC⟩, ⟨Subgroup.mem_subgroupOf.2 hxE, ?_⟩, rfl⟩
      show π ⟨x, hxC⟩ ∈ Subgroup.centralizer ((Lh.map π : Subgroup (↥Ce ⧸ θ)) : Set (↥Ce ⧸ θ))
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨l₀, hl₀, rfl⟩
      obtain ⟨t, ht, hteq⟩ := hxl (l₀ : G) (by rw [thetaLayer_eq]; exact ⟨l₀, hl₀, rfl⟩)
      have h4 : (⟨x, hxC⟩ * l₀ * ⟨x, hxC⟩⁻¹ * l₀⁻¹ : ↥Ce) = t := Subtype.ext (by simpa using hteq.symm)
      have h5 : π (⟨x, hxC⟩ * l₀ * ⟨x, hxC⟩⁻¹ * l₀⁻¹) = 1 := by rw [h4]; exact (QuotientGroup.eq_one_iff t).2 ht
      have h6 : π ⟨x, hxC⟩ * π l₀ * (π ⟨x, hxC⟩)⁻¹ * (π l₀)⁻¹ = 1 := by
        rw [← h5]; simp
      calc π l₀ * π ⟨x, hxC⟩ = (π ⟨x, hxC⟩ * π l₀ * (π ⟨x, hxC⟩)⁻¹ * (π l₀)⁻¹)⁻¹ *
            (π ⟨x, hxC⟩ * π l₀) := by group
        _ = π ⟨x, hxC⟩ * π l₀ := by rw [h6]; group
  have hNDH : ¬ IsCyclic ↥Dh → Subgroup.normalizer (Dh : Set ↥Ce) ≤ N₀.subgroupOf Ce := by
    intro hc
    have hcG : ¬ IsCyclic ↥(Dh.map Ce.subtype) := by
      intro hc'
      apply hc
      let eD := Dh.equivMapOfInjective Ce.subtype Ce.subtype_injective
      exact isCyclic_of_surjective eD.symm.toMonoidHom eD.symm.surjective
    exact Sec159Tr.normalizer_subgroupOf_le (hND _ hDmem hcG)
  have hY : ∀ y : ↥Ce, (∀ l ∈ Lh, y * l * y⁻¹ * l⁻¹ ∈ θ) → y ∈ N₀.subgroupOf Ce := by
    intro y hy
    refine Sec1510.Y_le_gen (V := θ) (Lh := Lh) (E := E.subgroupOf Ce) (P := P.subgroupOf Ce)
      (N₀ := N₀.subgroupOf Ce) (e := ⟨e, heC⟩) hθp hLlayer
      (fun M hMn hnil hMp => theta_quotient_nilpotent_bot hp hMn hnil hMp)
      (Subgroup.mem_subgroupOf.2 heE) (fun h => he1 (congrArg Subtype.val h))
      (fun h => Subtype.ext ((hmemCe h).1 h.2))
      (fun x hx => Subtype.ext (by simpa using hexp x (Subgroup.mem_subgroupOf.1 hx)))
      ⟨le_top, hPsyl.2.1.comap_subtype, by rw [Subgroup.relIndex_top_right]; exact hPsyl.2.2⟩
      (fun y hy => Subgroup.mem_subgroupOf.2 (hEP (Subgroup.mem_subgroupOf.1 hy)))
      (omegaOne_subgroupOf hEP hexp hPΩ)
      (fun x hx y hy => Subtype.ext
        (hPc x (Subgroup.mem_subgroupOf.1 hx) y (Subgroup.mem_subgroupOf.1 hy)))
      (fun y hy => Subgroup.mem_subgroupOf.2 (hPN (Subgroup.mem_subgroupOf.1 hy)))
      hVN
      (fun n hn => Subgroup.mem_subgroupOf.2 (hWN (mem_normalizer_of_subgroupOf hEC hn)))
      hNDH hInn' hy
  have hYc : ∀ y : ↥Ce, π y ∈ Subgroup.centralizer (layer (↥Ce ⧸ θ) : Set (↥Ce ⧸ θ)) →
      y ∈ N₀.subgroupOf Ce := by
    intro y hy
    refine hY y fun z hz => ?_
    have hz' : π z ∈ layer (↥Ce ⧸ θ) := by
      rw [← hLlayer]; exact Subgroup.mem_map_of_mem _ hz
    have h1 := Subgroup.mem_centralizer_iff.1 hy (π z) hz'
    have h3 : π (y * z * y⁻¹ * z⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have h2 : π y * π z = π z * π y := h1.symm
      calc π y * π z * (π y)⁻¹ * (π z)⁻¹ = π z * π y * (π y)⁻¹ * (π z)⁻¹ := by rw [h2]
        _ = 1 := by group
    exact (QuotientGroup.eq_one_iff _).1 h3
  have hLc : (layer (↥Ce ⧸ θ)).Characteristic := LocalCores.layer_characteristic (G := ↥Ce ⧸ θ)
  have hLn : (layer (↥Ce ⧸ θ)).Normal := inferInstance
  have hCn : (Subgroup.centralizer (layer (↥Ce ⧸ θ) : Set (↥Ce ⧸ θ))).Normal :=
    Sec1510.centralizer_layer_normal
  set H₁ : Subgroup ↥Ce :=
    (layer (↥Ce ⧸ θ) ⊔ Subgroup.centralizer (layer (↥Ce ⧸ θ) : Set (↥Ce ⧸ θ))).comap π with hH₁
  have hH₁n : H₁.Normal := Subgroup.Normal.comap inferInstance π
  have hEH₁ : E.subgroupOf Ce ≤ H₁ := by
    intro x hx
    obtain ⟨l, ⟨hlE, hlL⟩, c', ⟨hcE, hcC⟩, hxlc⟩ := hInn' x hx
    show π x ∈ layer (↥Ce ⧸ θ) ⊔ Subgroup.centralizer (layer (↥Ce ⧸ θ) : Set (↥Ce ⧸ θ))
    rw [hxlc, map_mul]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [← hLlayer]; exact Subgroup.mem_map_of_mem _ hlL
    · refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      rw [← hLlayer] at hz
      obtain ⟨z₀, hz₀, rfl⟩ := hz
      have h1 := Subgroup.mem_centralizer_iff.1 hcC z₀ hz₀
      rw [← map_mul, ← map_mul, h1]
  have hH₁N : H₁ ≤ N₀.subgroupOf Ce := by
    intro h hh
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.1
      (show π h ∈ layer (↥Ce ⧸ θ) ⊔ Subgroup.centralizer (layer (↥Ce ⧸ θ) : Set (↥Ce ⧸ θ)) from hh)
    rw [← hLlayer] at ha
    obtain ⟨l, hl, rfl⟩ := ha
    have hy : l⁻¹ * h ∈ N₀.subgroupOf Ce := by
      apply hYc
      have : π (l⁻¹ * h) = b := by
        rw [map_mul, map_inv, ← hab]; group
      rw [this]; exact hb
    have := (N₀.subgroupOf Ce).mul_mem (hLhN hl) hy
    simpa using this
  have hEH₁' : E ≤ H₁.map Ce.subtype := fun x hx =>
    ⟨⟨x, hEC hx⟩, hEH₁ (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hH₁N' : H₁.map Ce.subtype ≤ N₀ := by
    rintro _ ⟨h, hh, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hH₁N hh)
  exact Sec15FA.frattini_torus_le hp hE hJ hEH₁' (Subgroup.map_subtype_le H₁)
    (le_normalizer_map_subtype (N := H₁)) hH₁N' hWN

theorem centralizer_le {p : ℕ} (hp : p.Prime) {E P N₀ : Subgroup G} {e : G}
    (hE : IsElementaryAbelian p ↥E) (hEcard : Nat.card ↥E = p ^ 3)
    (hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E)
    (hWN : Subgroup.normalizer (E : Set G) ≤ N₀)
    (hN : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B → Subgroup.normalizer (B : Set G) ≤ N₀)
    (heE : e ∈ E) (he1 : e ≠ 1)
    (hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ N₀)
    (hInn : ∀ x ∈ E, ∃ l ∈ E ⊓ thetaLayer p e,
      ∃ c' ∈ E ⊓ Subgroup.centralizer (thetaLayer p e : Set G), x = l * c')
    (hPsyl : IsSylowOf p P (Subgroup.centralizer ({e} : Set G))) (hEP : E ≤ P) (hPN : P ≤ N₀)
    (hPΩ : omegaOne p P = E) (hPc : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x) :
    Subgroup.centralizer ({e} : Set G) ≤ N₀ :=
  centralizer_le_gen hp hE le_rfl hE hEcard hJ hWN hN
    (fun D hD hc => hN D (fun x hx => ((hD x).1 hx).1) hc) heE he1 hLN hInn hPsyl hEP hPN hPΩ hPc

omit [Finite G] in
theorem sylow_centralizes {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) [Finite G] {E P : Subgroup G}
    (hexp : ∀ e ∈ E, e ^ p = 1) {W₀ : Subgroup (MulAut E)} (hW : Weyl154 p E W₀)
    (hW4 : Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4))) (hP : IsPGroup p ↥P)
    (hPW : P ≤ Subgroup.normalizer (E : Set G)) : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxk : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact Sec159Aut.centralizes_of_pPower hp hp5 hexp hW hW4 (hPW hx) hxk y hy

theorem node1510Even_of_inputs (h154 : Node154) (h155 : Node155) (h158 : Node158)
    (h159 : Node159Even) (hInn : KFInnLayer) : Node1510Even := by
  classical
  intro G _ _ p A c L E h15 hF hout hEA U hUE hU1
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEcard : Nat.card ↥E = p ^ 3 := hEA ▸ h.A_card
  have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hN : ∀ B : Subgroup G, B ≤ E → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBE hBcyc =>
    h158 G p A c L E h15 hF hout B (hEA ▸ hBE) hBcyc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout hEQ hQW hQ
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  have hS : ∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set G) := by
    rw [hEA]; exact h.setup.2.2.2.2.2.2.2.2.1
  obtain ⟨W₀, hW⟩ := h154 G p A c L E h15 hF hout
  have hW4 := Sec159Node.weyl154_perm_four hEA hout hW
  have hCe : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ lieNormalizer p E := by
    intro e heE he1
    have hEC : E ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨e, heE⟩))
    obtain ⟨P, hPsyl, hEP, hPW, hPΩ⟩ :=
      Sec159Node.exists_sylow hp h155 (X := Subgroup.centralizer ({e} : Set G)) h15 hF hout hEA
    rw [sup_eq_left.2 hEC] at hPsyl
    have hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E := fun Z hZ =>
      h159 G p A c L E h15 hF hout hEA Z
        ⟨E, ⟨le_rfl, hEel, hEcard, hS⟩, mem_thetaComponentFamily_iff.2 ⟨e, heE, he1, hZ⟩⟩
    exact centralizer_le hp hEel hEcard hJ hWN hN heE he1 hLN
      (hInn G p A c L E h15 hF hout hEA e heE he1 hLN) hPsyl hEP (hPW.trans hWN) hPΩ
      (sylow_centralizes hp hp5 hexp hW hW4 hPsyl.2.1 hPW)
  obtain ⟨⟨e, heU⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have he1' : e ≠ 1 := fun h' => he1 (Subtype.ext h')
  have hC : Subgroup.centralizer (U : Set G) ≤ lieNormalizer p E :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 heU)).trans (hCe e (hUE heU) he1')
  exact Sec15FA.normalizer_le_of_centralizer_le hp hEel hJ hUE hWN hC

theorem node1510_of_inputs (h154 : Node154) (h155 : Node155) (h158 : Node158) (h159 : Node159Even)
    (hInn : KFInnLayer) (hFive : Node1510Five) : Node1510 :=
  node1510_of_cases (node1510Even_of_inputs h154 h155 h158 h159 hInn) hFive

end Sec1510Node

end CFSG.RankThree.PartOne
