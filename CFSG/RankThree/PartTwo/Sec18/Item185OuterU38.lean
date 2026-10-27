module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterBase
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
public import Certificates.Certificate185001
import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Generic

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.YGroups

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.RankThree.PartTwo.Sec4.Item434U38 (U38G X' strong1 base1 strong3 base3)

section OmegaToolkit

variable {G : Type} [Group G] [Finite G]

private theorem oTwoP_normal (p : ℕ) (H : Type*) [Group H] : (Sec4.oTwoP p H).Normal := by
  unfold Sec4.oTwoP
  exact Subgroup.Normal.comap CFSG.pCore_normal _

theorem oTwoP_conj_mem (H : Subgroup G) {h x : G} (hh : h ∈ H)
    (hx : x ∈ (Sec4.oTwoP 3 H).map H.subtype) :
    h * x * h⁻¹ ∈ (Sec4.oTwoP 3 H).map H.subtype := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
  exact Subgroup.mem_map.mpr
    ⟨⟨h, hh⟩ * m * ⟨h, hh⟩⁻¹, (oTwoP_normal 3 ↥H).conj_mem m hm ⟨h, hh⟩, rfl⟩

theorem exists_normal_sylow_two_of_le_oTwoP (H N : Subgroup G)
    (hN : N ≤ (Sec4.oTwoP 3 H).map H.subtype) : ∃ P : Sylow 2 N, (P : Subgroup N).Normal := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNH : N ≤ H := hN.trans (Subgroup.map_subtype_le _)
  let ψ : N →* H ⧸ CFSG.pCore 2 H :=
    (QuotientGroup.mk' (CFSG.pCore 2 H)).comp (Subgroup.inclusion hNH)
  have hker : IsPGroup 2 ψ.ker := by
    rintro ⟨x, hx⟩
    have hx' : Subgroup.inclusion hNH x ∈ CFSG.pCore 2 H :=
      (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := H) ⟨_, hx'⟩
    have h1 : (Subgroup.inclusion hNH x) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    refine ⟨k, Subtype.ext ?_⟩
    show x ^ 2 ^ k = 1
    apply Subgroup.inclusion_injective hNH
    rw [map_pow, map_one]
    exact h1
  have hrange : IsPGroup 3 ψ.range := by
    refine (CFSG.pCore_isPGroup (p := 3) (G := H ⧸ CFSG.pCore 2 H)).to_le ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp (hN x.2)
    have hxm : Subgroup.inclusion hNH x = m := Subtype.ext hmx.symm
    show QuotientGroup.mk' (CFSG.pCore 2 H) (Subgroup.inclusion hNH x) ∈ _
    rw [hxm]
    exact hm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hrange
  have hidx : ¬ 2 ∣ ψ.ker.index := by
    rw [Subgroup.index_ker, hn]
    intro h2
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
    omega
  exact ⟨hker.toSylow hidx, MonoidHom.normal_ker ψ⟩

private theorem false_of_two_elements {H B : Subgroup G}
    (hB : B ≤ (Sec4.oTwoP 3 H).map H.subtype) {h u u' u'' : G} (hh : h ∈ H) (hu : u ∈ B)
    (hu' : u' ∈ B) (hu'' : u'' ∈ B) (h1 : ((h * u * h⁻¹) * u') ^ 4 = 1)
    (h2 : (u * ((h * u' * h⁻¹) * u'')) ^ 4 = 1)
    (h3 : (((h * u * h⁻¹) * u') * (u * ((h * u' * h⁻¹) * u''))) ^ 3 = 1)
    (h4 : ((h * u * h⁻¹) * u') * (u * ((h * u' * h⁻¹) * u'')) ≠ 1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcu : h * u * h⁻¹ ∈ (Sec4.oTwoP 3 H).map H.subtype := oTwoP_conj_mem H hh (hB hu)
  have hcu' : h * u' * h⁻¹ ∈ (Sec4.oTwoP 3 H).map H.subtype := oTwoP_conj_mem H hh (hB hu')
  have hz1 : (h * u * h⁻¹) * u' ∈ (Sec4.oTwoP 3 H).map H.subtype :=
    Subgroup.mul_mem _ hcu (hB hu')
  have hz2 : u * ((h * u' * h⁻¹) * u'') ∈ (Sec4.oTwoP 3 H).map H.subtype :=
    Subgroup.mul_mem _ (hB hu) (Subgroup.mul_mem _ hcu' (hB hu''))
  generalize hz1def : (h * u * h⁻¹) * u' = z1 at *
  generalize hz2def : u * ((h * u' * h⁻¹) * u'') = z2 at *
  have hNO : Subgroup.closure {z1, z2} ≤ (Sec4.oTwoP 3 H).map H.subtype := by
    rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    exacts [hz1, hz2]
  obtain ⟨Q, hQ⟩ := exists_normal_sylow_two_of_le_oTwoP H _ hNO
  haveI := Sylow.unique_of_normal Q hQ
  have key : ∀ x : ↥(Subgroup.closure {z1, z2}), ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ (Q : Subgroup _) := by
    intro x k hxk
    have hz : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hxk)
    obtain ⟨S, hS⟩ := hz.exists_le_sylow
    have hSQ : S = Q := Subsingleton.elim S Q
    rw [← hSQ]
    exact hS (Subgroup.mem_zpowers x)
  let x1 : ↥(Subgroup.closure {z1, z2}) := ⟨z1, Subgroup.subset_closure (by simp)⟩
  let x2 : ↥(Subgroup.closure {z1, z2}) := ⟨z2, Subgroup.subset_closure (by simp)⟩
  have hx1 : x1 ∈ (Q : Subgroup _) := key x1 2 (Subtype.ext (by simpa [x1] using h1))
  have hx2 : x2 ∈ (Q : Subgroup _) := key x2 2 (Subtype.ext (by simpa [x2] using h2))
  obtain ⟨k, hk⟩ := Q.isPGroup' ⟨x1 * x2, Subgroup.mul_mem _ hx1 hx2⟩
  have hk' : (z1 * z2) ^ 2 ^ k = 1 := by
    have := congrArg (fun y : ↥(Q : Subgroup ↥(Subgroup.closure {z1, z2})) => ((y : _) : G)) hk
    simpa [x1, x2] using this
  have hd3 : orderOf (z1 * z2) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf (z1 * z2) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  exact h4 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd3 hd2))

end OmegaToolkit

noncomputable def oTwoThreeCentX' (c : Equiv.Perm (Fin 513)) : Subgroup (Equiv.Perm (Fin 513)) :=
  (Sec4.oTwoP 3 ↥((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X')).map
    ((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X').subtype

structure U38Data (P A B : Subgroup (Equiv.Perm (Fin 513))) (c : Equiv.Perm (Fin 513)) : Prop where
  le_Γ : P ≤ U38G
  isPGroup : IsPGroup 3 P
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P (P ⊔ X')
  card_le : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ 27
  isElemAbelian : IsElemAbelian 3 A
  card_A : Nat.card A = 27
  le_P : A ≤ P
  le_B : B ≤ A
  card_B : Nat.card B = 9
  eq_sup : A = Subgroup.zpowers c ⊔ B
  not_mem : c ∉ B
  le_inner : B ≤ X'
  dichotomy : (∀ x ∈ P, x * c = c * x) ∨
    ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
      ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 513))),
        x * c * x⁻¹ = b * c)
  omega : B ≤ oTwoThreeCentX' c
  outer : c ∉ X'

section Transport0

variable {G H : Type} [Group G] [Group H]

private theorem commute_of_isElemAbelian {p : ℕ} {E : Subgroup H} (hE : IsElemAbelian p E)
    {a b : H} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup H} (hE : IsElemAbelian p E)
    (hF : F ≤ E) : IsElemAbelian p F :=
  ⟨⟨⟨fun a b => Subtype.ext (commute_of_isElemAbelian hE (hF a.2) (hF b.2))⟩⟩,
    fun x hx => hE.2 x (hF hx)⟩

private theorem isElemAbelian_map_of_hom {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E)
    (f : G →* H) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, commute_of_isElemAbelian hE hx hy]
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    rw [← hxa, ← map_pow, hE.2 x hx, map_one]

private theorem isElemAbelian_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    {E : Subgroup H} (hE : IsElemAbelian 3 E) : IsElemAbelian 3 (E.comap f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    apply hf
    simp only [Subgroup.coe_mul, map_mul]
    exact commute_of_isElemAbelian hE (Subgroup.mem_comap.mp a.2) (Subgroup.mem_comap.mp b.2)
  · apply hf
    rw [map_pow, map_one]
    exact hE.2 (f x) (Subgroup.mem_comap.mp hx)

private theorem card_le_map_of_injective {f : G →* H} (hf : Function.Injective f) {P : Subgroup G}
    {n : ℕ} (hP : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ n) :
    ∀ E ≤ P.map f, IsElemAbelian 3 E → Nat.card E ≤ n := by
  intro E hE hEa
  have hEr : E ≤ f.range := fun y hy => by
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.mp (hE hy)
    exact MonoidHom.mem_range.mpr ⟨z, hz⟩
  have hle : E.comap f ≤ P := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hE (Subgroup.mem_comap.mp hx))
    rw [← hf hyx]
    exact hy
  have hcard : Nat.card E = Nat.card (E.comap f) := by
    have h1 := Subgroup.card_map_of_injective (K := E.comap f) hf
    rwa [Subgroup.map_comap_eq_self hEr] at h1
  rw [hcard]
  exact hP _ hle (isElemAbelian_comap_of_injective hf hEa)

private theorem isSylowOf_map_of_hom {G' : Type} [Group G'] [Finite G] {p : ℕ} [Fact p.Prime]
    (φ : G →* G') {P K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf p P K) :
    CFSG.ABGLocalTools.IsSylowOf p (P.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem dichotomy_map_of_injective {φ : G →* H} (hφ : Function.Injective φ)
    {P A B : Subgroup G} {c : G}
    (hd : (∀ x ∈ P, x * c = c * x) ∨
      ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
        ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set G), x * c * x⁻¹ = b * c)) :
    (∀ x ∈ P.map φ, x * φ c = φ c * x) ∨
      ((∀ x ∈ P.map φ, (∀ a ∈ A.map φ, x * a = a * x) → x ∈ A.map φ) ∧
        ∀ b ∈ B.map φ, ∃ x ∈ P.map φ ⊓ Subgroup.centralizer ((B.map φ : Subgroup H) : Set H),
          x * φ c * x⁻¹ = b * φ c) := by
  rcases hd with h1 | ⟨h2, h3⟩
  · left
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h1 y hy]
  · right
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩ hcomm
      have hyA : y ∈ A := h2 y hy (fun a ha => hφ (by
        have := hcomm (φ a) (Subgroup.mem_map_of_mem φ ha)
        simpa only [map_mul] using this))
      exact Subgroup.mem_map_of_mem φ hyA
    · intro b hb
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
      obtain ⟨x, ⟨hxP, hxC⟩, hxc⟩ := h3 b' hb'
      refine ⟨φ x, Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem φ hxP, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have hh' : h ∈ B.map φ := hh
        obtain ⟨b'', hb'', rfl⟩ := Subgroup.mem_map.mp hh'
        have hc := Subgroup.mem_centralizer_iff.mp hxC b'' hb''
        rw [← map_mul, ← map_mul, hc]
      · have := congrArg φ hxc
        simpa only [map_mul, map_inv] using this

end Transport0

private theorem oTwoP_map_subtype_eq {K₁ K₂ : Type} [Group K₁] [Group K₂] [Finite K₁]
    (φ : K₁ →* K₂) (hφ : Function.Injective φ) {F : Subgroup K₁} {C : Subgroup K₂}
    (hFC : F.map φ = C) :
    ((Sec4.oTwoP 3 ↥F).map F.subtype).map φ = (Sec4.oTwoP 3 ↥C).map C.subtype := by
  let e : ↥F ≃* ↥C := (Subgroup.equivMapOfInjective F φ hφ).trans (MulEquiv.subgroupCongr hFC)
  have h1 := oTwoP_map_mulEquiv e
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem U38Data.of_map {G : Type} [Group G] [Finite G] (φ : G →* Equiv.Perm (Fin 513))
    (hφ : Function.Injective φ) {K : Subgroup G} (hK : K.map φ = X') {P A B : Subgroup G} {c : G}
    (hΓ : P.map φ ≤ U38G) (hP : IsPGroup 3 P) (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 P (P ⊔ K))
    (hle : ∀ E ≤ P, IsElemAbelian 3 E → Nat.card E ≤ 27) (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hAP : A ≤ P) (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hsup : A = Subgroup.zpowers c ⊔ B) (hcB : c ∉ B) (hBK : B ≤ K)
    (hd : (∀ x ∈ P, x * c = c * x) ∨
      ((∀ x ∈ P, (∀ a ∈ A, x * a = a * x) → x ∈ A) ∧
        ∀ b ∈ B, ∃ x ∈ P ⊓ Subgroup.centralizer (B : Set G), x * c * x⁻¹ = b * c))
    (hom : ∀ b ∈ B, φ b ∈ oTwoThreeCentX' (φ c)) (hout : c ∉ K) :
    U38Data (P.map φ) (A.map φ) (B.map φ) (φ c) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact
    { le_Γ := hΓ
      isPGroup := hP.map φ
      sylow := by
        have h1 := isSylowOf_map_of_hom φ hsyl
        rw [Subgroup.map_sup, hK] at h1
        exact h1
      card_le := card_le_map_of_injective hφ hle
      isElemAbelian := isElemAbelian_map_of_hom hA φ
      card_A := by rw [Subgroup.card_map_of_injective hφ]; exact hA27
      le_P := Subgroup.map_mono hAP
      le_B := Subgroup.map_mono hBA
      card_B := by rw [Subgroup.card_map_of_injective hφ]; exact hB9
      eq_sup := by
        have h1 := congrArg (Subgroup.map φ) hsup
        rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h1
        exact h1
      not_mem := fun hm => hcB ((Subgroup.mem_map_iff_mem hφ).mp hm)
      le_inner := (Subgroup.map_mono hBK).trans hK.le
      dichotomy := dichotomy_map_of_injective hφ hd
      omega := by
        rintro _ ⟨b, hb, rfl⟩
        exact hom b hb
      outer := fun hm => hout ((Subgroup.mem_map_iff_mem hφ).mp (by rw [hK]; exact hm)) }

private theorem X'_le_U38G : X' ≤ U38G := by
  unfold X' U38G arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk7 : k < 7 := by rw [Sec4.Item434U38.gensX_size] at hk; exact hk
  apply Subgroup.subset_closure
  refine ⟨k, by rw [Sec4.Item434U38.gensO_size]; omega, ?_⟩
  rw [Sec4.Item434U38.gensX_getElem k hk7]

section Transport

theorem OuterData.toU38Data {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* projSU 3 2 3))
    {P A B : Subgroup (MulAut X)} {c : MulAut X} (h : OuterData X P A B c) :
    ∃ (P' A' B' : Subgroup (Equiv.Perm (Fin 513))) (c' : Equiv.Perm (Fin 513)),
      U38Data P' A' B' c' := by
  obtain ⟨eX⟩ := Sec4.Item434U38.nonempty_equiv_X' hX
  let κ : U38G ≃* MulAut X' :=
    MulEquiv.ofBijective Sec4.Item434U38.rhoU38 (Sec4.Item434U38.rhoU38_bijective hX)
  let ι : MulAut X →* Equiv.Perm (Fin 513) :=
    U38G.subtype.comp (κ.symm.toMonoidHom.comp (MulAut.congr eX).toMonoidHom)
  have hι_inj : Function.Injective ι :=
    Subtype.val_injective.comp (κ.symm.injective.comp (MulAut.congr eX).injective)
  have hι_mem : ∀ σ : MulAut X, ι σ ∈ U38G := fun σ => (κ.symm (MulAut.congr eX σ)).2
  have hκ : ∀ (g : U38G) (y : X'), ((κ g y : X') : Equiv.Perm (Fin 513)) =
      (g : Equiv.Perm (Fin 513)) * y * (g : Equiv.Perm (Fin 513))⁻¹ :=
    fun g y => Sec4.Item434U38.rhoU38_apply g y
  have hι_spec : ∀ (σ : MulAut X) (x : X),
      ι σ * ((eX x : X') : Equiv.Perm (Fin 513)) * (ι σ)⁻¹ = ((eX (σ x) : X') : Equiv.Perm (Fin 513)) := by
    intro σ x
    have h1 := hκ (κ.symm (MulAut.congr eX σ)) (eX x)
    rw [κ.apply_symm_apply] at h1
    have h2 : (MulAut.congr eX σ) (eX x) = eX (σ x) := by
      show eX (σ (eX.symm (eX x))) = eX (σ x)
      rw [MulEquiv.symm_apply_apply]
    rw [h2] at h1
    exact h1.symm
  have hι_conj : ∀ x : X, ι (MulAut.conj x) = ((eX x : X') : Equiv.Perm (Fin 513)) := by
    intro x
    have h1 : κ ⟨((eX x : X') : Equiv.Perm (Fin 513)), X'_le_U38G (eX x).2⟩ = MulAut.conj (eX x) :=
      MulEquiv.ext fun y => Subtype.ext (hκ _ y)
    have h2 : κ.symm (MulAut.congr eX (MulAut.conj x)) =
        ⟨((eX x : X') : Equiv.Perm (Fin 513)), X'_le_U38G (eX x).2⟩ := by
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, ← h1, κ.symm_apply_apply]
    show ((κ.symm (MulAut.congr eX (MulAut.conj x)) : U38G) : Equiv.Perm (Fin 513)) = _
    rw [h2]
  have hK : (innerAut X).map ι = X' := by
    ext g
    constructor
    · rintro ⟨σ, ⟨x, rfl⟩, rfl⟩
      rw [hι_conj]
      exact (eX x).2
    · intro hg
      refine ⟨MulAut.conj (eX.symm ⟨g, hg⟩), ⟨_, rfl⟩, ?_⟩
      rw [hι_conj]
      simp
  have hΓ : P.map ι ≤ U38G := by
    rintro _ ⟨σ, -, rfl⟩
    exact hι_mem σ
  let φ₁ : X →* Equiv.Perm (Fin 513) := X'.subtype.comp eX.toMonoidHom
  have hφ₁ : Function.Injective φ₁ := Subtype.val_injective.comp eX.injective
  have hFC : (fixedSubgroup c).map φ₁ =
      Subgroup.centralizer ({ι c} : Set (Equiv.Perm (Fin 513))) ⊓ X' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, (eX x).2⟩
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have h1 := hι_spec c x
      have hx' : c x = x := hx
      rw [hx'] at h1
      show ι c * ((eX x : X') : Equiv.Perm (Fin 513)) = ((eX x : X') : Equiv.Perm (Fin 513)) * ι c
      calc ι c * ((eX x : X') : Equiv.Perm (Fin 513))
          = ι c * ((eX x : X') : Equiv.Perm (Fin 513)) * (ι c)⁻¹ * ι c := by group
        _ = ((eX x : X') : Equiv.Perm (Fin 513)) * ι c := by rw [h1]
    · rintro ⟨hy1, hy2⟩
      refine ⟨eX.symm ⟨y, hy2⟩, ?_, by simp [φ₁]⟩
      have hcomm : ι c * y = y * ι c := Subgroup.mem_centralizer_iff.mp hy1 (ι c) rfl
      have h1 := hι_spec c (eX.symm ⟨y, hy2⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      have h2 : ((eX (c (eX.symm ⟨y, hy2⟩)) : X') : Equiv.Perm (Fin 513)) = y := by
        rw [← h1]
        calc ι c * y * (ι c)⁻¹ = y * ι c * (ι c)⁻¹ := by rw [hcomm]
          _ = y := by group
      show c (eX.symm ⟨y, hy2⟩) = eX.symm ⟨y, hy2⟩
      apply eX.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext h2
  have hom : ∀ b ∈ B, ι b ∈ oTwoThreeCentX' (ι c) := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (h.omega hb)
    rw [hι_conj]
    have h1 := oTwoP_map_subtype_eq φ₁ hφ₁ hFC
    have h2 : φ₁ x ∈ ((Sec4.oTwoP 3 ↥(fixedSubgroup c)).map (fixedSubgroup c).subtype).map φ₁ :=
      Subgroup.mem_map_of_mem φ₁ hx
    rw [h1] at h2
    exact h2
  exact ⟨P.map ι, A.map ι, B.map ι, ι c,
    U38Data.of_map ι hι_inj hK hΓ h.isPGroup h.sylow h.card_le h.isElemAbelian h.card_A h.le_P
      h.le_B h.card_B h.eq_sup h.not_mem h.le_inner h.dichotomy hom h.outer⟩

end Transport

section Soundness

private theorem ps_lt : ∀ p ∈ U38Elim.ps, p < 513 := by
  intro p hp
  simp only [U38Elim.ps, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> norm_num

private theorem checkWith_parts {gs : Array (Array ℕ)} {cR : ArrCert} {hs : Array (Array ℕ)}
    (h : U38Elim.checkWith gs cR hs = true) :
    enumOK 513 gs U38Elim.ps cR = true ∧ cR.pts.size = 729 ∧ U38Elim.genOK gs = true ∧
      U38Elim.tabOK cR.pts (U38Elim.mulTab cR.pts) = true ∧
      (U38Elim.flagged (U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts) cR.pts.size).length = 81 ∧
      U38Elim.hsOK (rawLevels 513 strong3 base3) hs = true ∧
      U38Elim.d1OK (U38Elim.mulTab cR.pts) (U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts)
        cR.pts.size = true ∧
      U38Elim.triplesOK cR.pts hs (U38Elim.mulTab cR.pts)
        (U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts) = true := by
  simp only [U38Elim.checkWith, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

private theorem point_inj {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) {i j : ℕ} (hi : i < cR.pts.size)
    (hj : j < cR.pts.size)
    (h : permOfArr 513 cR.pts[i]! = permOfArr 513 cR.pts[j]!) : i = j := by
  obtain ⟨-, -, hval⟩ := enumOK_spec ps_lt hE
  have hc : arrCertOK (leftA 513 gs) gs.size (validA 513) (keyA 513 U38Elim.ps) (idA 513) cR = true := by
    simp only [enumOK, Bool.and_eq_true] at hE
    exact hE.2
  exact arrCertOK_keys_inj hc hi hj (keyA_eq ps_lt (hval i hi) (hval j hj) h)

private theorem point_zero {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) : permOfArr 513 cR.pts[0]! = 1 := by
  have hc : arrCertOK (leftA 513 gs) gs.size (validA 513) (keyA 513 U38Elim.ps) (idA 513) cR = true := by
    simp only [enumOK, Bool.and_eq_true] at hE
    exact hE.2
  rw [arrCertOK_root hc]
  exact permOfArr_eq_of_rep rep_idA

private theorem keyA_eq_of_rep {a b : Array ℕ} {g : Equiv.Perm (Fin 513)} (ha : Rep 513 a g)
    (hb : Rep 513 b g) : keyA 513 U38Elim.ps a = keyA 513 U38Elim.ps b := by
  unfold keyA
  refine congrArg (Nat.ofDigits 513) (List.map_congr_left fun p hp => ?_)
  rw [ha.apply (ps_lt p hp), hb.apply (ps_lt p hp)]

private theorem keyProd_eq (E : Array (Array ℕ)) (i j : ℕ) :
    U38Elim.keyProd E i j = keyA 513 U38Elim.ps (compA 513 E[i]! E[j]!) := by
  unfold U38Elim.keyProd keyA
  refine congrArg (Nat.ofDigits 513) (List.map_congr_left fun p hp => ?_)
  rw [compA_get (ps_lt p hp)]

private theorem tab_spec {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true)
    {T : Array (Array ℕ)} (hT : U38Elim.tabOK cR.pts T = true) {i j : ℕ} (hi : i < cR.pts.size)
    (hj : j < cR.pts.size) :
    U38Elim.mulI T i j < cR.pts.size ∧
      permOfArr 513 cR.pts[U38Elim.mulI T i j]! =
        permOfArr 513 cR.pts[i]! * permOfArr 513 cR.pts[j]! := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec ps_lt hE
  have h1 := allLt_spec (allLt_spec hT hi) hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  obtain ⟨hlt, hkey⟩ := h1
  refine ⟨hlt, ?_⟩
  have hxR : permOfArr 513 cR.pts[i]! * permOfArr 513 cR.pts[j]! ∈
      Subgroup.closure (permsA 513 gs) :=
    mul_mem ((hmem _).2 ⟨i, hi, rfl⟩) ((hmem _).2 ⟨j, hj, rfl⟩)
  obtain ⟨k, hk, hkx⟩ := (hmem _).1 hxR
  have hc : arrCertOK (leftA 513 gs) gs.size (validA 513) (keyA 513 U38Elim.ps) (idA 513) cR = true := by
    simp only [enumOK, Bool.and_eq_true] at hE
    exact hE.2
  have hkk : keyA 513 U38Elim.ps cR.pts[k]! = keyA 513 U38Elim.ps cR.pts[U38Elim.mulI T i j]! := by
    rw [hkey, keyProd_eq]
    refine keyA_eq_of_rep (g := permOfArr 513 cR.pts[i]! * permOfArr 513 cR.pts[j]!) ?_ ?_
    · rw [← hkx]
      exact rep_of_validA (hval k hk)
    · exact rep_compA (rep_of_validA (hval i hi)) (rep_of_validA (hval j hj))
  have hkm : k = U38Elim.mulI T i j := arrCertOK_keys_inj hc hk hlt hkk
  rw [← hkm]
  exact hkx

private theorem arrClosure_le_U38G {gs : Array (Array ℕ)} (h : U38Elim.genOK gs = true) :
    arrClosure 513 gs ≤ U38G := by
  unfold arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have h1 := allLt_spec h hk
  simp only [Bool.and_eq_true] at h1
  exact Sec4.Item434U38.mem_U38G_of_sift1 h1.1 h1.2

private theorem hs_mem {hs : Array (Array ℕ)}
    (h : U38Elim.hsOK (rawLevels 513 strong3 base3) hs = true) {k : ℕ} (hk : k < hs.size) :
    validA 513 hs[k]! = true ∧ permOfArr 513 hs[k]! ∈ X' := by
  have h1 := allLt_spec h hk
  simp only [Bool.and_eq_true] at h1
  exact ⟨h1.1, Sec4.Item434U38.sift3_mem (rep_of_validA h1.1) h1.2⟩

private theorem flag_mem {E : Array (Array ℕ)} (hval : ∀ i < E.size, validA 513 E[i]! = true) {i : ℕ}
    (hi : i < E.size)
    (hix : (U38Elim.inXArr (rawLevels 513 strong3 base3) E)[i]! = true) :
    permOfArr 513 E[i]! ∈ X' := by
  have h1 : siftA 513 (rawLevels 513 strong3 base3) base3 0 E[i]! = true := by
    unfold U38Elim.inXArr at hix
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos E i hi] at hix
    exact hix
  exact Sec4.Item434U38.sift3_mem (rep_of_validA (hval i hi)) h1

private theorem inf_X'_facts {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) (hsz : cR.pts.size = 729)
    (hfl : (U38Elim.flagged (U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts)
      cR.pts.size).length = 81) :
    Nat.card (arrClosure 513 gs ⊓ X' : Subgroup (Equiv.Perm (Fin 513))) = 81 ∧
      ∀ i < cR.pts.size, permOfArr 513 cR.pts[i]! ∈ X' →
        (U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts)[i]! = true := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec ps_lt hE
  set ix := U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts with hix
  set S0 : Subgroup (Equiv.Perm (Fin 513)) := arrClosure 513 gs ⊓ X' with hS0def
  have hle : Nat.card S0 ≤ 81 := by
    have h1 : Nat.card S0 ∣ Nat.card (arrClosure 513 gs) := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card S0 ∣ Nat.card X' := Subgroup.card_dvd_of_le inf_le_right
    have hRcard : Nat.card (arrClosure 513 gs) = 729 := by rw [← hsz]; exact hcard
    rw [hRcard] at h1
    rw [Sec4.Item434U38.card_X'] at h2
    have h3 : Nat.card S0 ∣ Nat.gcd 729 5515776 := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 729 5515776 = 81 := by norm_num
    rw [h4] at h3
    exact Nat.le_of_dvd (by norm_num) h3
  have hmemR : ∀ i < cR.pts.size, permOfArr 513 cR.pts[i]! ∈ arrClosure 513 gs := fun i hi =>
    (hmem _).2 ⟨i, hi, rfl⟩
  have hcnt : ∀ F : Finset ℕ, (∀ i ∈ F, i < cR.pts.size ∧ permOfArr 513 cR.pts[i]! ∈ S0) →
      F.card ≤ Nat.card S0 := by
    intro F hF
    have hinj : Function.Injective
        (fun i : F => (⟨permOfArr 513 cR.pts[i.1]!, (hF i.1 i.2).2⟩ : S0)) := by
      intro i1 i2 h12
      exact Subtype.ext (point_inj hE (hF _ i1.2).1 (hF _ i2.2).1 (congrArg Subtype.val h12))
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_finsetCard] at this
  let F : Finset ℕ := (U38Elim.flagged ix cR.pts.size).toFinset
  have hFmem : ∀ i ∈ F, i < cR.pts.size ∧ ix[i]! = true := by
    intro i hi
    simp only [F, U38Elim.flagged, List.mem_toFinset, List.mem_filter, List.mem_range] at hi
    exact hi
  have hFS : ∀ i ∈ F, i < cR.pts.size ∧ permOfArr 513 cR.pts[i]! ∈ S0 := fun i hi =>
    ⟨(hFmem i hi).1, hmemR i (hFmem i hi).1, flag_mem hval (hFmem i hi).1 (hFmem i hi).2⟩
  have hFcard : F.card = 81 := by
    simp only [F]
    rw [List.toFinset_card_of_nodup, hfl]
    exact (List.nodup_range).filter _
  have hge : 81 ≤ Nat.card S0 := hFcard ▸ hcnt F hFS
  have hS0 : Nat.card S0 = 81 := le_antisymm hle hge
  refine ⟨hS0, fun i hi hX => ?_⟩
  by_contra hnot
  have hnotF : i ∉ F := fun hF => hnot (hFmem i hF).2
  have h82 := hcnt (insert i F) (by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact ⟨hi, hmemR k hi, hX⟩
    · exact hFS k hk)
  rw [Finset.card_insert_of_notMem hnotF, hFcard] at h82
  omega

private theorem commI_iff {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) {T : Array (Array ℕ)}
    (hT : U38Elim.tabOK cR.pts T = true) {i j : ℕ} (hi : i < cR.pts.size) (hj : j < cR.pts.size) :
    U38Elim.commI T i j = true ↔
      permOfArr 513 cR.pts[i]! * permOfArr 513 cR.pts[j]! =
        permOfArr 513 cR.pts[j]! * permOfArr 513 cR.pts[i]! := by
  unfold U38Elim.commI
  rw [beq_iff_eq]
  obtain ⟨hl1, h1⟩ := tab_spec hE hT hi hj
  obtain ⟨hl2, h2⟩ := tab_spec hE hT hj hi
  constructor
  · intro h
    rw [← h1, ← h2, h]
  · intro h
    exact point_inj hE hl1 hl2 (by rw [h1, h2, h])

private theorem cubeI_of_pow {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) {T : Array (Array ℕ)}
    (hT : U38Elim.tabOK cR.pts T = true) {i : ℕ} (hi : i < cR.pts.size)
    (h : permOfArr 513 cR.pts[i]! ^ 3 = 1) : U38Elim.cubeI T i = true := by
  unfold U38Elim.cubeI
  rw [beq_iff_eq]
  obtain ⟨hl1, h1⟩ := tab_spec hE hT hi hi
  obtain ⟨hl2, h2⟩ := tab_spec hE hT hi hl1
  refine point_inj hE hl2 (Nat.lt_of_le_of_lt (Nat.zero_le i) hi) ?_
  rw [h2, h1, point_zero hE, ← pow_three]
  exact h

private theorem d1_spec {T : Array (Array ℕ)} {ix : Array Bool} {N : ℕ}
    (h : U38Elim.d1OK T ix N = true) {j : ℕ} (hj : j < N) (hjx : ix[j]! = false) :
    ∃ s ∈ U38Elim.flagged ix N, U38Elim.commI T j s = false := by
  unfold U38Elim.d1OK at h
  have h1 := allLt_spec h hj
  simp only [hjx, Bool.false_or, List.any_eq_true, Bool.not_eq_true'] at h1
  exact h1

private theorem refD2_spec {T : Array (Array ℕ)} {cen bel : List ℕ} {j : ℕ}
    (h : U38Elim.refD2 T cen bel j = true) :
    ∃ b ∈ bel, ∀ x ∈ cen, U38Elim.mulI T x j ≠ U38Elim.mulI T (U38Elim.mulI T b j) x := by
  unfold U38Elim.refD2 at h
  simp only [List.any_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h

private theorem belems_mem {gs : Array (Array ℕ)} {cR : ArrCert}
    (hE : enumOK 513 gs U38Elim.ps cR = true) {T : Array (Array ℕ)}
    (hT : U38Elim.tabOK cR.pts T = true) {B : Subgroup (Equiv.Perm (Fin 513))} {i1 i2 : ℕ}
    (hi1 : i1 < cR.pts.size) (hi2 : i2 < cR.pts.size)
    (h1 : permOfArr 513 cR.pts[i1]! ∈ B) (h2 : permOfArr 513 cR.pts[i2]! ∈ B) :
    ∀ b ∈ U38Elim.belems T i1 i2, b < cR.pts.size ∧ permOfArr 513 cR.pts[b]! ∈ B := by
  have hmul : ∀ a b, a < cR.pts.size → permOfArr 513 cR.pts[a]! ∈ B → b < cR.pts.size →
      permOfArr 513 cR.pts[b]! ∈ B →
      U38Elim.mulI T a b < cR.pts.size ∧ permOfArr 513 cR.pts[U38Elim.mulI T a b]! ∈ B := by
    intro a b ha hpa hb hpb
    obtain ⟨hl, hp⟩ := tab_spec hE hT ha hb
    exact ⟨hl, by rw [hp]; exact mul_mem hpa hpb⟩
  have h0 : 0 < cR.pts.size := Nat.lt_of_le_of_lt (Nat.zero_le _) hi1
  have hs1 := hmul i1 i1 hi1 h1 hi1 h1
  have hs2 := hmul i2 i2 hi2 h2 hi2 h2
  intro b hb
  unfold U38Elim.belems at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨h0, by rw [point_zero hE]; exact one_mem B⟩
  · exact ⟨hi1, h1⟩
  · exact hs1
  · exact ⟨hi2, h2⟩
  · exact hmul _ _ hi1 h1 hi2 h2
  · exact hmul _ _ hs1.1 hs1.2 hi2 h2
  · exact hs2
  · exact hmul _ _ hi1 h1 hs2.1 hs2.2
  · exact hmul _ _ hs1.1 hs1.2 hs2.1 hs2.2

private theorem omegaOK_spec {E hs : Array (Array ℕ)} {bel : List ℕ} {j : ℕ}
    (h : U38Elim.omegaOK E hs bel j = true) :
    (∀ l ∈ U38Elim.wLetters, l ∈ bel) ∧ ∃ hi, U38Elim.witOK E hs hi j = true := by
  unfold U38Elim.omegaOK at h
  rw [List.any_eq_true] at h
  obtain ⟨w, -, hw⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨⟨-, hl⟩, hw⟩ := hw
  exact ⟨fun l hl' => by simpa using hl l hl', w.2, hw⟩

private theorem pow_four_of_mul {G : Type*} [Group G] {z : G} (h : z * z * (z * z) = 1) :
    z ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  exact h

private theorem pow_three_of_mul {G : Type*} [Group G] {p : G} (h : p * (p * p) = 1) :
    p ^ 3 = 1 := by
  rw [pow_three]
  exact h

private theorem witOK_spec {E hs : Array (Array ℕ)} {hi j : ℕ}
    (hw : U38Elim.witOK E hs hi j = true) (hvh : validA 513 hs[hi]! = true)
    {c u u' u'' : Equiv.Perm (Fin 513)} (hc : Rep 513 E[j]! c) (hu : Rep 513 E[247]! u)
    (hu' : Rep 513 E[263]! u') (hu'' : Rep 513 E[282]! u'') :
    permOfArr 513 hs[hi]! * c = c * permOfArr 513 hs[hi]! ∧
      ((permOfArr 513 hs[hi]! * u * (permOfArr 513 hs[hi]!)⁻¹) * u') ^ 4 = 1 ∧
      (u * ((permOfArr 513 hs[hi]! * u' * (permOfArr 513 hs[hi]!)⁻¹) * u'')) ^ 4 = 1 ∧
      (((permOfArr 513 hs[hi]! * u * (permOfArr 513 hs[hi]!)⁻¹) * u') *
        (u * ((permOfArr 513 hs[hi]! * u' * (permOfArr 513 hs[hi]!)⁻¹) * u''))) ^ 3 = 1 ∧
      ((permOfArr 513 hs[hi]! * u * (permOfArr 513 hs[hi]!)⁻¹) * u') *
        (u * ((permOfArr 513 hs[hi]! * u' * (permOfArr 513 hs[hi]!)⁻¹) * u'')) ≠ 1 := by
  have hh : Rep 513 hs[hi]! (permOfArr 513 hs[hi]!) := rep_of_validA hvh
  have hz1 := rep_compA (rep_conjA hvh hu) hu'
  have hz2 := rep_compA hu (rep_compA (rep_conjA hvh hu') hu'')
  have hp := rep_compA hz1 hz2
  simp only [U38Elim.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hw
  refine ⟨(eqA_iff (rep_compA hh hc) (rep_compA hc hh)).1 h1,
    pow_four_of_mul ((eqA_iff (rep_compA (rep_compA hz1 hz1) (rep_compA hz1 hz1)) rep_idA).1 h2),
    pow_four_of_mul ((eqA_iff (rep_compA (rep_compA hz2 hz2) (rep_compA hz2 hz2)) rep_idA).1 h3),
    pow_three_of_mul ((eqA_iff (rep_compA hp (rep_compA hp hp)) rep_idA).1 h4), fun hp1 => ?_⟩
  have := (eqA_iff hp rep_idA).2 hp1
  rw [this] at h5
  exact absurd h5 (by decide)

private theorem triples_spec {E hs T : Array (Array ℕ)} {ix : Array Bool}
    (h : U38Elim.triplesOK E hs T ix = true) {i1 i2 j : ℕ}
    (hi1 : i1 < E.size) (hi2 : i2 < E.size) (hj : j < E.size)
    (h1x : ix[i1]! = true) (h10 : i1 ≠ 0) (h1c : U38Elim.cubeI T i1 = true)
    (h2x : ix[i2]! = true) (h20 : i2 ≠ 0) (h2c : U38Elim.cubeI T i2 = true)
    (h12 : U38Elim.commI T i1 i2 = true) (hne1 : i2 ≠ i1) (hne2 : i2 ≠ U38Elim.mulI T i1 i1)
    (hjx : ix[j]! = false) (hjc : U38Elim.cubeI T j = true)
    (hj1 : U38Elim.commI T j i1 = true) (hj2 : U38Elim.commI T j i2 = true) :
    U38Elim.refD2 T (U38Elim.cenOf T E.size i1 i2) (U38Elim.belems T i1 i2) j = true ∨
      U38Elim.omegaOK E hs (U38Elim.belems T i1 i2) j = true := by
  unfold U38Elim.triplesOK at h
  dsimp only at h
  have hm1 : i1 ∈ (List.range E.size).filter
      fun i => ix[i]! && i != 0 && U38Elim.cubeI T i := by
    simp [List.mem_filter, hi1, h1x, h10, h1c]
  have hm2 : i2 ∈ (List.range E.size).filter
      fun i => ix[i]! && i != 0 && U38Elim.cubeI T i := by
    simp [List.mem_filter, hi2, h2x, h20, h2c]
  have hmj : j ∈ (List.range E.size).filter fun j => !ix[j]! && U38Elim.cubeI T j := by
    simp [List.mem_filter, hj, hjx, hjc]
  have h2' := List.all_eq_true.mp (List.all_eq_true.mp h i1 hm1) i2 hm2
  have hcond : (U38Elim.commI T i1 i2 && i2 != i1 && i2 != U38Elim.mulI T i1 i1) = true := by
    simp [h12, hne1, hne2]
  simp only [hcond, Bool.not_true, Bool.false_or] at h2'
  have h3' := List.all_eq_true.mp h2' j hmj
  simp only [hj1, hj2, Bool.and_self, Bool.not_true, Bool.false_or, Bool.or_eq_true] at h3'
  exact h3'

private theorem witOK_lt {E hs : Array (Array ℕ)} {hi j : ℕ}
    (hw : U38Elim.witOK E hs hi j = true) : hi < hs.size := by
  simp only [U38Elim.witOK, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hw
  exact hw.1.1.1.1.1

private theorem factorization_three_X' : (5515776 : ℕ).factorization 3 = 4 := by
  have h : (5515776 : ℕ) = 3 ^ 4 * 68096 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), Nat.add_zero]

private theorem factorization_three_U38G : (99283968 : ℕ).factorization 3 = 6 := by
  have h : (99283968 : ℕ) = 3 ^ 6 * 136192 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), Nat.add_zero]

private theorem facts_of_check {gs : Array (Array ℕ)} {cR : ArrCert} {ws : Array (Array ℕ)}
    (hchk : U38Elim.checkWith gs cR ws = true) :
    arrClosure 513 gs ≤ U38G ∧ Nat.card (arrClosure 513 gs) = 729 ∧
      Nat.card (arrClosure 513 gs ⊓ X' : Subgroup (Equiv.Perm (Fin 513))) = 81 := by
  obtain ⟨hE, hsz, hgen, -, hfl, -⟩ := checkWith_parts hchk
  refine ⟨arrClosure_le_U38G hgen, ?_, (inf_X'_facts hE hsz hfl).1⟩
  have h1 := (enumOK_spec ps_lt hE).2.1
  rw [hsz] at h1
  exact h1

private theorem false_of_check {gs : Array (Array ℕ)} {cR : ArrCert} {ws : Array (Array ℕ)}
    (hchk : U38Elim.checkWith gs cR ws = true) {P A B : Subgroup (Equiv.Perm (Fin 513))}
    {c : Equiv.Perm (Fin 513)} (hP : P ≤ arrClosure 513 gs) (h : U38Data P A B c) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE, hsz, hgen, hT0, hfl, hhs, hd1, htr⟩ := checkWith_parts hchk
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec ps_lt hE
  obtain ⟨hS0card, hflag⟩ := inf_X'_facts hE hsz hfl
  set T := U38Elim.mulTab cR.pts with hTdef
  set ix := U38Elim.inXArr (rawLevels 513 strong3 base3) cR.pts with hixdef
  have hmem' : ∀ x, x ∈ arrClosure 513 gs ↔ ∃ i < cR.pts.size, permOfArr 513 cR.pts[i]! = x := hmem
  have hRle : arrClosure 513 gs ≤ U38G := arrClosure_le_U38G hgen
  have hPΓ : P ≤ U38G := hP.trans hRle
  have hnorm : P ⊔ X' ≤ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) :=
    sup_le (hPΓ.trans Sec4.Item434U38.U38G_le_normalizer) Subgroup.le_normalizer
  have hsyl := h.sylow.inf_of_le_normalizer le_sup_right hnorm
  have hPX : Nat.card (P ⊓ X' : Subgroup (Equiv.Perm (Fin 513))) = 81 := by
    rw [hsyl.card_eq, Sec4.Item434U38.card_X', factorization_three_X']
    norm_num
  have hS0P : arrClosure 513 gs ⊓ X' ≤ P := by
    have h1 : P ⊓ X' ≤ arrClosure 513 gs ⊓ X' := inf_le_inf_right _ hP
    have h2 : P ⊓ X' = arrClosure 513 gs ⊓ X' :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hS0card, hPX])
    rw [← h2]
    exact inf_le_left
  have hcA : c ∈ A := by
    rw [h.eq_sup]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hcR : c ∈ arrClosure 513 gs := hP (h.le_P hcA)
  obtain ⟨jc, hjc, hjcc⟩ := (hmem' c).1 hcR
  have hjx : ix[jc]! = false := by
    cases hx : ix[jc]! with
    | false => rfl
    | true => exact absurd (hjcc ▸ flag_mem hval hjc hx) h.outer
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c hcA
  have hjcube : U38Elim.cubeI T jc = true := cubeI_of_pow hE hT0 hjc (by rw [hjcc]; exact hc3)
  rcases h.dichotomy with hcentral | ⟨-, hB'⟩
  ·
    obtain ⟨s, hsF, hsc⟩ := d1_spec hd1 hjc hjx
    simp only [U38Elim.flagged, List.mem_filter, List.mem_range] at hsF
    obtain ⟨hslt, hsx⟩ := hsF
    have hsR : permOfArr 513 cR.pts[s]! ∈ arrClosure 513 gs := (hmem' _).2 ⟨s, hslt, rfl⟩
    have hsX : permOfArr 513 cR.pts[s]! ∈ X' := flag_mem hval hslt hsx
    have hsP : permOfArr 513 cR.pts[s]! ∈ P := hS0P ⟨hsR, hsX⟩
    have hcomm := hcentral _ hsP
    have hcs : U38Elim.commI T jc s = true := by
      rw [commI_iff hE hT0 hjc hslt, hjcc]
      exact hcomm.symm
    rw [hcs] at hsc
    exact absurd hsc (by decide)
  ·
    have hBel : IsElemAbelian 3 B := isElemAbelian_of_le h.isElemAbelian h.le_B
    obtain ⟨b1, b2, hb1B, hb2B, hb11, hb13, hb23, hb12, hb2s, -⟩ :=
      Sec19.TrialityTwo.exists_gen_pair
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hBel) (by rw [h.card_B]; norm_num)
    have hpt : ∀ x ∈ B, ∃ i < cR.pts.size, permOfArr 513 cR.pts[i]! = x ∧ ix[i]! = true := by
      intro x hx
      obtain ⟨i, hi, hix⟩ := (hmem' x).1 (hP (h.le_P (h.le_B hx)))
      exact ⟨i, hi, hix, hflag i hi (by rw [hix]; exact h.le_inner hx)⟩
    obtain ⟨i1, hi1, hi1b, hi1x⟩ := hpt b1 hb1B
    obtain ⟨i2, hi2, hi2b, hi2x⟩ := hpt b2 hb2B
    have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      commute_of_isElemAbelian h.isElemAbelian hx hy
    have hi10 : i1 ≠ 0 := by
      rintro rfl
      exact hb11 (by rw [← hi1b, point_zero hE])
    have hi20 : i2 ≠ 0 := by
      rintro rfl
      exact hb2s (by rw [← hi2b, point_zero hE]; simp)
    have hne1 : i2 ≠ i1 := by
      rintro rfl
      exact hb2s (by rw [← hi2b, hi1b]; simp)
    have hne2 : i2 ≠ U38Elim.mulI T i1 i1 := by
      intro hh
      obtain ⟨-, hp⟩ := tab_spec hE hT0 hi1 hi1
      have hb2eq : b2 = b1 * b1 := by rw [← hi2b, hh, hp, hi1b]
      exact hb2s (by simp [hb2eq])
    have h12 : U38Elim.commI T i1 i2 = true := by
      rw [commI_iff hE hT0 hi1 hi2, hi1b, hi2b]
      exact hb12
    have hi1c : U38Elim.cubeI T i1 = true := cubeI_of_pow hE hT0 hi1 (by rw [hi1b]; exact hb13)
    have hi2c : U38Elim.cubeI T i2 = true := cubeI_of_pow hE hT0 hi2 (by rw [hi2b]; exact hb23)
    have hj1 : U38Elim.commI T jc i1 = true := by
      rw [commI_iff hE hT0 hjc hi1, hjcc, hi1b]
      exact hcommA c hcA b1 (h.le_B hb1B)
    have hj2 : U38Elim.commI T jc i2 = true := by
      rw [commI_iff hE hT0 hjc hi2, hjcc, hi2b]
      exact hcommA c hcA b2 (h.le_B hb2B)
    have hB1 : permOfArr 513 cR.pts[i1]! ∈ B := by rw [hi1b]; exact hb1B
    have hB2 : permOfArr 513 cR.pts[i2]! ∈ B := by rw [hi2b]; exact hb2B
    have hbel := belems_mem hE hT0 hi1 hi2 hB1 hB2
    rcases triples_spec htr hi1 hi2 hjc hi1x hi10 hi1c hi2x hi20 hi2c h12 hne1 hne2 hjx hjcube hj1
      hj2 with hr | ho
    ·
      obtain ⟨bb, hbb, hx⟩ := refD2_spec hr
      obtain ⟨hbblt, hbbB⟩ := hbel bb hbb
      obtain ⟨x, ⟨hxP, hxC⟩, hxc⟩ := hB' _ hbbB
      obtain ⟨k, hk, hkx⟩ := (hmem' x).1 (hP hxP)
      have hxb1 : x * b1 = b1 * x := (Subgroup.mem_centralizer_iff.mp hxC b1 hb1B).symm
      have hxb2 : x * b2 = b2 * x := (Subgroup.mem_centralizer_iff.mp hxC b2 hb2B).symm
      have hkcen : k ∈ U38Elim.cenOf T cR.pts.size i1 i2 := by
        simp only [U38Elim.cenOf, List.mem_filter, List.mem_range, Bool.and_eq_true]
        refine ⟨hk, ?_, ?_⟩
        · rw [commI_iff hE hT0 hk hi1, hkx, hi1b]
          exact hxb1
        · rw [commI_iff hE hT0 hk hi2, hkx, hi2b]
          exact hxb2
      apply hx k hkcen
      obtain ⟨hl1, hp1⟩ := tab_spec hE hT0 hk hjc
      obtain ⟨hl2, hp2⟩ := tab_spec hE hT0 hbblt hjc
      obtain ⟨hl3, hp3⟩ := tab_spec hE hT0 hl2 hk
      refine point_inj hE hl1 hl3 ?_
      rw [hp1, hp3, hp2, hkx, hjcc]
      calc x * c = (x * c * x⁻¹) * x := by group
        _ = (permOfArr 513 cR.pts[bb]! * c) * x := by rw [hxc]
    ·
      obtain ⟨hlet, hi, hw⟩ := omegaOK_spec ho
      have hlt := witOK_lt hw
      obtain ⟨hvh, hhX⟩ := hs_mem hhs hlt
      obtain ⟨h247, u1B⟩ := hbel 247 (hlet 247 (by simp [U38Elim.wLetters]))
      obtain ⟨h263, u2B⟩ := hbel 263 (hlet 263 (by simp [U38Elim.wLetters]))
      obtain ⟨h282, u3B⟩ := hbel 282 (hlet 282 (by simp [U38Elim.wLetters]))
      have hcRep : Rep 513 cR.pts[jc]! c := by
        rw [← hjcc]
        exact rep_of_validA (hval jc hjc)
      obtain ⟨hcomm, e1, e2, e3, e4⟩ := witOK_spec hw hvh hcRep
        (rep_of_validA (hval 247 h247)) (rep_of_validA (hval 263 h263))
        (rep_of_validA (hval 282 h282))
      have hH : permOfArr 513 ws[hi]! ∈
          (Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X' := by
        refine ⟨Subgroup.mem_centralizer_iff.mpr fun z hz => ?_, hhX⟩
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact hcomm.symm
      exact false_of_two_elements (H := (Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X')
        h.omega hH u1B u2B u3B e1 e2 e3 e4

end Soundness

section Elimination

noncomputable def u38R : Subgroup (Equiv.Perm (Fin 513)) := arrClosure 513 U38Elim.rGens

theorem u38R_facts : u38R ≤ U38G ∧ Nat.card u38R = 729 ∧ Nat.card (u38R ⊓ X' : Subgroup _) = 81 :=
  facts_of_check (gs := U38Elim.rGens ()) (cR := U38Elim.rCert ()) (ws := U38Elim.hList ())
    Certificates.certificate185001

theorem u38_sylow_reduction {P : Subgroup (Equiv.Perm (Fin 513))} (hP : P ≤ U38G)
    (h3 : IsPGroup 3 P) : ∃ g ∈ U38G, P.map (MulAut.conj g).toMonoidHom ≤ u38R := by
  obtain ⟨hRΓ, hR729, -⟩ := u38R_facts
  have hS : Nat.card (u38R.subgroupOf U38G) = 3 ^ (Nat.card U38G).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv, hR729,
      Sec4.Item434U38.card_U38G, factorization_three_U38G]
    norm_num
  have hE : IsPGroup 3 (P.subgroupOf U38G) := h3.comap_subtype
  obtain ⟨g, hg⟩ := Sec19.TrialityTwo.exists_conj_le_sylow hS hE
  refine ⟨g.1, g.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact hg ⟨x, hP hx⟩ hx

theorem U38Data.conj {P A B : Subgroup (Equiv.Perm (Fin 513))}
    {c : Equiv.Perm (Fin 513)} (h : U38Data P A B c) {g : Equiv.Perm (Fin 513)} (hg : g ∈ U38G) :
    U38Data (P.map (MulAut.conj g).toMonoidHom) (A.map (MulAut.conj g).toMonoidHom)
      (B.map (MulAut.conj g).toMonoidHom) (g * c * g⁻¹) := by
  have hgN : g ∈ Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) :=
    Sec4.Item434U38.U38G_le_normalizer hg
  let φ : Equiv.Perm (Fin 513) →* Equiv.Perm (Fin 513) := (MulAut.conj g).toMonoidHom
  have hφ : Function.Injective φ := (MulAut.conj g).injective
  have hφx : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
  have hK : X'.map φ = X' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hφx]
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by rw [hφx]; group⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * y * g)).mpr
        (by rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]; exact hy)
  have hFC : ((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X').map φ =
      (Subgroup.centralizer ({φ c} : Set (Equiv.Perm (Fin 513)))) ⊓ X' := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxc, hxX⟩, rfl⟩
      refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        have hcx : c * x = x * c := Subgroup.mem_centralizer_iff.mp hxc c rfl
        rw [← map_mul, ← map_mul, hcx]
      · rw [hφx]
        exact (Subgroup.mem_normalizer_iff.mp hgN x).mp hxX
    · rintro ⟨hy1, hy2⟩
      have hcomm : φ c * y = y * φ c := Subgroup.mem_centralizer_iff.mp hy1 (φ c) rfl
      rw [hφx] at hcomm
      refine ⟨g⁻¹ * y * g, ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩, by rw [hφx]; group⟩
      · intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        calc z * (g⁻¹ * y * g) = g⁻¹ * (g * z * g⁻¹ * y) * g := by group
          _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hcomm]
          _ = (g⁻¹ * y * g) * z := by group
      · exact (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * y * g)).mpr
          (by rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]; exact hy2)
  have hΓ : P.map φ ≤ U38G := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hφx]
    exact mul_mem (mul_mem hg (h.le_Γ hx)) (inv_mem hg)
  have hom : ∀ b ∈ B, φ b ∈ oTwoThreeCentX' (φ c) := by
    intro b hb
    have h1 := oTwoP_map_subtype_eq φ hφ hFC
    have h2 : φ b ∈ ((Sec4.oTwoP 3 ↥((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X')).map
        ((Subgroup.centralizer ({c} : Set (Equiv.Perm (Fin 513)))) ⊓ X').subtype).map φ :=
      Subgroup.mem_map_of_mem φ (h.omega hb)
    rw [h1] at h2
    exact h2
  exact U38Data.of_map φ hφ hK hΓ h.isPGroup h.sylow h.card_le h.isElemAbelian h.card_A h.le_P
    h.le_B h.card_B h.eq_sup h.not_mem h.le_inner h.dichotomy hom h.outer

theorem u38_enumeration {P A B : Subgroup (Equiv.Perm (Fin 513))} {c : Equiv.Perm (Fin 513)}
    (hP : P ≤ u38R) (h : U38Data P A B c) : False :=
  false_of_check (gs := U38Elim.rGens ()) (cR := U38Elim.rCert ()) (ws := U38Elim.hList ())
    Certificates.certificate185001 hP h

theorem no_u38Data {P A B : Subgroup (Equiv.Perm (Fin 513))} {c : Equiv.Perm (Fin 513)}
    (h : U38Data P A B c) : False := by
  obtain ⟨g, hg, hgP⟩ := u38_sylow_reduction h.le_Γ h.isPGroup
  exact u38_enumeration hgP (h.conj hg)

end Elimination

theorem noOuterData_projSU_three_eight :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSU 3 2 3) → NoOuterData X := by
  intro X _ _ hX P A B c hd
  obtain ⟨P', A', B', c', h'⟩ := hd.toU38Data hX
  exact no_u38Data h'

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
