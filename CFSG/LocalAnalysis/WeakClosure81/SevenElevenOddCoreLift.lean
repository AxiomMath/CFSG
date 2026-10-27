module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

namespace OddCoreLiftSC

private theorem odd_card_fusionOddCore (X : Type) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem le_fusionOddCore {X : Type} [Group X] {N : Subgroup X} (hN : N.Normal)
    (ho : Odd (Nat.card N)) : N ≤ fusionOddCore X :=
  le_sSup ⟨hN, ho⟩

private theorem eq_one_of_mul_self {X : Type} [Group X] [Finite X] {u : X}
    (hu : u ∈ fusionOddCore X) (h2 : u * u = 1) : u = 1 := by
  have hdvd1 : orderOf (⟨u, hu⟩ : fusionOddCore X) ∣ Nat.card (fusionOddCore X) :=
    orderOf_dvd_natCard _
  have hdvd2 : orderOf (⟨u, hu⟩ : fusionOddCore X) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [pow_two, h2]))
  have h1 : orderOf (⟨u, hu⟩ : fusionOddCore X) = 1 :=
    Nat.eq_one_of_dvd_coprimes (odd_card_fusionOddCore X).coprime_two_left hdvd2 hdvd1
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp h1)

private theorem fusionOddCore_eq_comap {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hk : Odd (Nat.card f.ker)) :
    fusionOddCore A = (fusionOddCore B).comap f := by
  haveI : Finite B := Finite.of_surjective f hf
  apply le_antisymm
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_fusionOddCore ((fusionOddCore_normal A).map f hf)
      ((odd_card_fusionOddCore A).of_dvd_nat (Subgroup.card_map_dvd _ f))
  · refine le_fusionOddCore ((fusionOddCore_normal B).comap f) ?_
    set K := (fusionOddCore B).comap f
    let g : K →* fusionOddCore B := f.subgroupComap (fusionOddCore B)
    have hg : Function.Surjective g := by
      rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨⟨a, hb⟩, rfl⟩
    rw [← Subgroup.card_ker_mul_card_of_surjective hg]
    refine Nat.odd_mul.mpr ⟨?_, odd_card_fusionOddCore B⟩
    refine hk.of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective (K := g.ker) K.subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hx

private theorem mem_fusionZStar_iff' {A : Type} [Group A] (x : A) :
    x ∈ fusionZStar A ↔ ∀ g : A, x * g * x⁻¹ * g⁻¹ ∈ fusionOddCore A := by
  unfold fusionZStar
  rw [mem_comap, mem_center_iff]
  constructor
  · intro h g
    have := h (g : A ⧸ fusionOddCore A)
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk'_apply] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, this]
  · intro h g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    have := h g
    rw [← QuotientGroup.eq_one_iff] at this
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    simpa [QuotientGroup.mk'_apply] using this.symm

private theorem fusionZStar_eq_comap {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hO : fusionOddCore A = (fusionOddCore B).comap f) :
    fusionZStar A = (fusionZStar B).comap f := by
  ext x
  rw [mem_comap, mem_fusionZStar_iff', mem_fusionZStar_iff', hO]
  simp only [mem_comap, map_mul, map_inv]
  constructor
  · intro h g
    obtain ⟨g, rfl⟩ := hf g
    exact h g
  · intro h g
    exact h (f g)

private theorem nonempty_zstar_equiv {A B : Type} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hZ : fusionZStar A = (fusionZStar B).comap f) :
    Nonempty (A ⧸ fusionZStar A ≃* B ⧸ fusionZStar B) := by
  let g := (QuotientGroup.mk' (fusionZStar B)).comp f
  have hg : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hf
  have hk : g.ker = fusionZStar A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hZ]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

private theorem isL2OrSz_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsL2OrSz A n) : IsL2OrSz B n := by
  unfold IsL2OrSz CFSG.Quasithin.IsPSL CFSG.Quasithin.IsSz StatedClassicalModel
    CFSG.Blueprint.SuzukiModel at h ⊢
  rcases h with ⟨h1, K, hK, hfin, hc, ⟨e'⟩⟩ | ⟨h1, a, ha, K, hK, hfin, hf, hc, ⟨e'⟩⟩
  · exact Or.inl ⟨h1, K, hK, hfin, hc, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨h1, a, ha, K, hK, hfin, hf, hc, ⟨e.symm.trans e'⟩⟩

private theorem exists_not_commute {X : Type} [Group X] (s : X)
    (hgen : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hO : ¬ fusionOddCore X ≤ Subgroup.center X) :
    ∃ y ∈ fusionOddCore X, y * s ≠ s * y := by
  by_contra hcon
  push Not at hcon
  apply hO
  have hs : s ∈ Subgroup.centralizer (fusionOddCore X : Set X) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact hcon h hh
  have hle : Subgroup.normalClosure ({s} : Set X) ≤
      Subgroup.centralizer (fusionOddCore X : Set X) :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hs)
  rw [hgen] at hle
  intro z hz
  rw [mem_center_iff]
  intro g
  exact ((mem_centralizer_iff.mp (hle (mem_top g))) z hz).symm

private theorem dihedral_conj {G : Type*} [Group G] {t d : G} (ht : t * t = 1) (hd : d * d = 1)
    {n : ℕ} (hn : Odd n) (hr : (t * d) ^ n = 1) :
    ∃ j : ℕ, d = ((t * d) ^ j)⁻¹ * t * (t * d) ^ j := by
  obtain ⟨m, rfl⟩ := hn
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have h1 : t * (t * d) * t⁻¹ = (t * d)⁻¹ := by
    rw [htinv, mul_inv_rev, hdinv, htinv, ← mul_assoc, ht, one_mul]
  have h2 : ∀ k : ℕ, t * (t * d) ^ k * t⁻¹ = ((t * d) ^ k)⁻¹ := by
    intro k
    rw [← conj_pow, h1, inv_pow]
  refine ⟨m + 1, ?_⟩
  have h3 : ((t * d) ^ (m + 1))⁻¹ * t = t * (t * d) ^ (m + 1) := by
    rw [← h2]; group
  rw [h3, mul_assoc, ← pow_add]
  have : m + 1 + (m + 1) = (2 * m + 1) + 1 := by ring
  rw [this, pow_succ, hr, one_mul, ← mul_assoc, ht, one_mul]

private theorem step {X Q : Type} [Group X] [Group Q] (π : X →* Q) (Lh : Subgroup Q) {s t : X}
    (hsLh : π s ∈ Lh) (hgenLh : normalClosure ({⟨π s, hsLh⟩} : Set Lh) = ⊤)
    (hconj : ∀ M : Subgroup X, s ∈ M → t ∈ M → ∃ c ∈ M, t = c⁻¹ * s * c)
    (M : Subgroup X) (hMP : M ≤ Lh.comap π) (hs : s ∈ M) (ht : t ∈ M) (hmap : M.map π = Lh) :
    (normalClosure ({⟨s, hs⟩} : Set M)).map M.subtype ≤ M ∧
      s ∈ (normalClosure ({⟨s, hs⟩} : Set M)).map M.subtype ∧
      t ∈ (normalClosure ({⟨s, hs⟩} : Set M)).map M.subtype ∧
      ((normalClosure ({⟨s, hs⟩} : Set M)).map M.subtype).map π = Lh := by
  set N := normalClosure ({⟨s, hs⟩} : Set M) with hN
  have hsN : (⟨s, hs⟩ : M) ∈ N := subset_normalClosure (Set.mem_singleton _)
  refine ⟨?_, ⟨⟨s, hs⟩, hsN, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · obtain ⟨c, hc, htc⟩ := hconj M hs ht
    refine ⟨⟨t, ht⟩, ?_, rfl⟩
    have : (⟨t, ht⟩ : M) = (⟨c, hc⟩ : M)⁻¹ * ⟨s, hs⟩ * (⟨c, hc⟩ : M)⁻¹⁻¹ := by
      rw [inv_inv]; exact Subtype.ext htc
    rw [this]
    exact (normalClosure_normal).conj_mem _ hsN _
  · let f : M →* Lh := (π.comp M.subtype).codRestrict Lh (fun x => hMP x.2)
    have hf : Function.Surjective f := by
      rintro ⟨y, hy⟩
      rw [← hmap] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨⟨x, hx⟩, rfl⟩
    have hcomp : π.comp M.subtype = Lh.subtype.comp f := by ext; rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hN, Subgroup.map_normalClosure _ f hf,
      Set.image_singleton]
    have : f ⟨s, hs⟩ = ⟨π s, hsLh⟩ := rfl
    rw [this, hgenLh, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end OddCoreLiftSC

open OddCoreLiftSC in
theorem oddCoreLiftL2SzSC :
    ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
      Subgroup.normalClosure ({s} : Set X) = ⊤ →
      ¬ fusionOddCore X ≤ Subgroup.center X →
      (∃ Lh : Subgroup (X ⧸ fusionOddCore X), ∃ hsLh : QuotientGroup.mk' (fusionOddCore X) s ∈ Lh,
        Subgroup.normalClosure ({⟨_, hsLh⟩} : Set ↥Lh) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥Lh ⧸ fusionZStar ↥Lh) n) →
      ∃ L : Subgroup X, ∃ hsL : s ∈ L,
        Subgroup.normalClosure ({⟨s, hsL⟩} : Set ↥L) = ⊤ ∧
        ∃ n : ℕ, 1 < n ∧ IsL2OrSz (↥L ⧸ fusionZStar ↥L) n ∧
          ¬ fusionOddCore ↥L ≤ Subgroup.center ↥L := by
  intro X _ _ s hs hgen hO ⟨Lh, hsLh, hgenLh, n, hn, hL2⟩
  set O := fusionOddCore X with hOdef
  set π := QuotientGroup.mk' O with hπ
  set P := Lh.comap π with hP
  obtain ⟨y, hyO, hys⟩ := exists_not_commute s hgen hO
  have hss : s * s = 1 := by
    rw [← pow_two, ← hs]; exact pow_orderOf_eq_one s
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hyπ : π y = 1 := (QuotientGroup.eq_one_iff _).mpr hyO
  set t := y * s * y⁻¹ with htdef
  have htt : t * t = 1 := by
    calc t * t = y * (s * s) * y⁻¹ := by rw [htdef]; group
      _ = 1 := by rw [hss, mul_one, mul_inv_cancel]
  have hstO : s * t ∈ O := by
    have : s * t = (s * y * s⁻¹) * y⁻¹ := by rw [htdef, hsinv]; group
    rw [this]
    exact O.mul_mem ((fusionOddCore_normal X).conj_mem _ hyO s) (O.inv_mem hyO)
  have hpow : (s * t) ^ Nat.card O = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := O) (x := ⟨s * t, hstO⟩))
  obtain ⟨j, hj⟩ := dihedral_conj hss htt (odd_card_fusionOddCore X) hpow
  have hconj : ∀ M : Subgroup X, s ∈ M → t ∈ M → ∃ c ∈ M, t = c⁻¹ * s * c :=
    fun M hsM htM => ⟨(s * t) ^ j, M.pow_mem (M.mul_mem hsM htM) j, hj⟩
  have hsP : s ∈ P := hsLh
  have htπ : π t = π s := by rw [htdef, map_mul, map_mul, map_inv, hyπ, inv_one, one_mul, mul_one]
  have htP : t ∈ P := by
    change π t ∈ Lh
    rw [htπ]; exact hsLh
  let S : Set (Subgroup X) := {M | M ≤ P ∧ s ∈ M ∧ t ∈ M ∧ M.map π = Lh}
  have hPS : P ∈ S := ⟨le_rfl, hsP, htP,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O) Lh⟩
  obtain ⟨L, ⟨hLP, hsL, htL, hmapL⟩, hmin⟩ := (Set.toFinite S).exists_minimal ⟨P, hPS⟩
  have hgenL : Subgroup.normalClosure ({⟨s, hsL⟩} : Set ↥L) = ⊤ := by
    obtain ⟨h1, h2, h3, h4⟩ := step π Lh hsLh hgenLh hconj L hLP hsL htL hmapL
    have hS' : (normalClosure ({⟨s, hsL⟩} : Set L)).map L.subtype ∈ S :=
      ⟨h1.trans hLP, h2, h3, h4⟩
    have heq := le_antisymm h1 (hmin hS' h1)
    rw [eq_top_iff]
    intro x _
    have hx : (x : X) ∈ (normalClosure ({⟨s, hsL⟩} : Set L)).map L.subtype := by
      rw [heq]; exact x.2
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = x := Subtype.ext hwx
    rwa [← this]
  let f : L →* Lh := (π.comp L.subtype).codRestrict Lh (fun x => hLP x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hmapL] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ∀ x : L, x ∈ f.ker ↔ (x : X) ∈ O := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp this
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hkodd : Odd (Nat.card f.ker) := by
    refine (odd_card_fusionOddCore X).of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective (K := f.ker) L.subtype_injective]
    apply Subgroup.card_dvd_of_le
    rintro _ ⟨x, hx, rfl⟩
    exact (hker x).mp hx
  have hOL := fusionOddCore_eq_comap f hf hkodd
  have hZL := fusionZStar_eq_comap f hf hOL
  obtain ⟨e⟩ := nonempty_zstar_equiv f hf hZL
  refine ⟨L, hsL, hgenL, n, hn, isL2OrSz_of_mulEquiv e.symm hL2, ?_⟩
  set u := y * s * y⁻¹ * s⁻¹ with hu
  have huL : u ∈ L := L.mul_mem htL (L.inv_mem hsL)
  have huO : u ∈ O := by
    have : u = y * (s * y⁻¹ * s⁻¹) := by rw [hu]; group
    rw [this]
    exact O.mul_mem hyO ((fusionOddCore_normal X).conj_mem _ (O.inv_mem hyO) s)
  have hus : u * s ≠ s * u := by
    intro hc
    apply hys
    have hconj : s * u * s⁻¹ = u⁻¹ := by
      have h1 : s * u * s⁻¹ = s * y * s * y⁻¹ * (s * s) := by
        rw [hu, hsinv]; group
      rw [h1, hss, mul_one, hu, hsinv]
      simp only [mul_inv_rev, inv_inv, hsinv, mul_assoc]
    have hu1 : s * u * s⁻¹ = u := by
      rw [← hc]; group
    have huu : u * u = 1 := by
      have : u = u⁻¹ := hu1.symm.trans hconj
      calc u * u = u * u⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel u
    have h1 : u = 1 := eq_one_of_mul_self huO huu
    rw [hu] at h1
    have h2 : y * s * y⁻¹ = s := by
      calc y * s * y⁻¹ = y * s * y⁻¹ * s⁻¹ * s := by group
        _ = s := by rw [h1, one_mul]
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [h2]
  intro hcen
  have hk : (⟨u, huL⟩ : L) ∈ fusionOddCore L := by
    rw [hOL, mem_comap]
    have : f ⟨u, huL⟩ = 1 := (hker _).mpr huO
    rw [this]
    exact (fusionOddCore Lh).one_mem
  have := mem_center_iff.mp (hcen hk) ⟨s, hsL⟩
  exact hus (congrArg Subtype.val this).symm

end CFSG.LocalAnalysis.WeakClosure81

end
