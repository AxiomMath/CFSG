module

public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallBCenter
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.LieType.Steinberg.CentralExt.CoprimeSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

@[expose] def GGPSections (p : ℕ) (H : Type) [Group H] : Prop :=
  ∀ (E : Type) [Group E] [Finite E] (η : E →* H), Function.Surjective η →
    η.ker ≤ Subgroup.center E → IsPGroup p η.ker → ∃ σ : H →* E, ∀ h, η (σ h) = h

@[expose] def GGModelLayerCyclic (p : ℕ) {H : Type} [Group H] (α : MulAut H) : Prop :=
  α ≠ 1 → α ^ p = 1 → IsComponentOf (LargeEvenLayer (ggFix α)) (ggFix α) →
    ∀ S : Subgroup H, S ≤ LargeEvenLayer (ggFix α) →
      S ≤ Subgroup.centralizer (LargeEvenLayer (ggFix α) : Set H) → IsPGroup p S → IsCyclic S

namespace LayerCC

section Lemmas

variable {H R : Type*} [Group H] [Group R]

theorem map_pow_apply {π : H →* R} {α : MulAut H} {φ : MulAut R}
    (h : ∀ x, π (α x) = φ (π x)) (n : ℕ) (x : H) : π ((α ^ n) x) = (φ ^ n) (π x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

theorem eq_one_of_map_eq {π : H →* R} (hker : π.ker ≤ Subgroup.center H)
    (hperf : commutator H = ⊤) {α : MulAut H} (h : ∀ x, π (α x) = π x) : α = 1 := by
  have hP : Group.IsPerfect H := ⟨hperf⟩
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq π hker hP α.toMonoidHom
    (MonoidHom.id H) h
  ext x
  exact key x

theorem eq_one_of_comp_eq {π : H →* R} (hπ : Function.Surjective π) {φ : MulAut R}
    (h : ∀ x, φ (π x) = π x) : φ = 1 := by
  ext r
  obtain ⟨x, rfl⟩ := hπ r
  exact h x

theorem injective_of_isPGroup {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]
    {C : Subgroup L} (hC : C ≤ Subgroup.center L) {S : Subgroup L} (hS : IsPGroup p S) :
    Function.Injective
      ((QuotientGroup.mk' (CoprimeSplit.copPart p C hC)).comp S.subtype) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hN : (s : L) ∈ CoprimeSplit.copPart p C hC := by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hs
    exact hs
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS) s
  have hcop : p.Coprime (orderOf (s : L)) := hN.2
  rw [Subgroup.orderOf_coe, hk] at hcop
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · exact absurd ((Nat.coprime_pow_right_iff (Nat.succ_pos k) p p).mp hcop)
      (Nat.Prime.coprime_iff_not_dvd hp.out |>.not.mpr (not_not.mpr (dvd_refl p)))

end Lemmas

end LayerCC

open LayerCC in
theorem ggLayerCenterCyclic_of_model {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} {H : Type} [Group H] [Finite H] (π : H →* R)
    (hπ : Function.Surjective π) (hπker : π.ker ≤ Subgroup.center H) (hH : commutator H = ⊤)
    (hsec : GGPSections p H)
    (hlift : ∀ φ ∈ I, ∃ α : MulAut H, (∀ h, π (α h) = φ (π h)) ∧ GGModelLayerCyclic p α) :
    GGLayerCenterCyclic p R I := by
  have := Fact.mk hp
  intro L' _ _ ψ hψ hker hperf _ a ha1 hap hind hcomp S hSK hSC hSp
  obtain ⟨φ, hφI, hφ⟩ := hind
  obtain ⟨α, hαπ, hmodel⟩ := hlift φ hφI
  set N := CoprimeSplit.copPart p ψ.ker hker with hN
  have hNker : N ≤ ψ.ker := fun _ h => h.1
  set q : L' →* L' ⧸ N := QuotientGroup.mk' N with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hqker : q.ker ≤ Subgroup.center L' := by
    rw [hq, QuotientGroup.ker_mk']
    exact hNker.trans hker
  set ψ'' : L' ⧸ N →* R := QuotientGroup.lift N ψ hNker with hψ''
  have hψ''q : ∀ l : L', ψ'' (l : L' ⧸ N) = ψ l := fun l => rfl
  have hψ''s : Function.Surjective ψ'' := fun r => by
    obtain ⟨l, rfl⟩ := hψ r
    exact ⟨(l : L' ⧸ N), rfl⟩
  have hker'' : ψ''.ker ≤ Subgroup.center (L' ⧸ N) := by
    intro y hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hl : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ''q]
      exact hy
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨z', rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hl) z']
  have hp'' : IsPGroup p ψ''.ker := by
    rintro ⟨y, hy⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hl : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ''q]
      exact hy
    obtain ⟨k, hk⟩ := CoprimeSplit.exists_pow_prime_pow_mem_copPart (p := p) hker hl
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have haker : ∀ l, l ∈ ψ.ker → a l ∈ ψ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    rw [← hφ, hl, map_one]
  have hainvker : ∀ l, l ∈ ψ.ker → a⁻¹ l ∈ ψ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : φ (ψ (a⁻¹ l)) = 1 := by rw [hφ, MulAut.apply_inv_self, hl]
    exact (map_eq_one_iff φ φ.injective).mp h1
  have haN : N.map (a : L' →* L') = N := by
    ext l
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨haker m hm.1, ?_⟩
      show p.Coprime (orderOf (a m))
      rw [MulEquiv.orderOf_eq]
      exact hm.2
    · intro hl
      refine ⟨a⁻¹ l, ⟨hainvker l hl.1, ?_⟩, ?_⟩
      · rw [MulEquiv.orderOf_eq]
        exact hl.2
      · show a (a⁻¹ l) = l
        rw [MulAut.apply_inv_self]
  set a'' : MulAut (L' ⧸ N) := QuotientGroup.congr N N a haN with ha''
  have ha''q : ∀ l : L', a'' (l : L' ⧸ N) = ((a l : L') : L' ⧸ N) := fun l => rfl
  have ha''ψ : ∀ y, ψ'' (a'' y) = φ (ψ'' y) := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    rw [ha''q, hψ''q, hψ''q]
    exact (hφ l).symm
  let Pb : Subgroup ((L' ⧸ N) × H) :=
    MonoidHom.eqLocus (ψ''.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _))
  let η : Pb →* H := (MonoidHom.snd _ _).comp Pb.subtype
  have hη : Function.Surjective η := by
    intro h
    obtain ⟨y, hy⟩ := hψ''s (π h)
    exact ⟨⟨(y, h), hy⟩, rfl⟩
  have hηker : η.ker ≤ Subgroup.center Pb := by
    rintro ⟨⟨y, h⟩, hx⟩ hk
    have hh : h = 1 := hk
    have hy : y ∈ ψ''.ker := by
      have hx' : ψ'' y = π h := hx
      rw [MonoidHom.mem_ker, hx', hh, map_one]
    rw [Subgroup.mem_center_iff]
    rintro ⟨⟨y', h'⟩, -⟩
    apply Subtype.ext
    change (y' * y, h' * h) = (y * y', h * h')
    rw [hh, one_mul, mul_one, Subgroup.mem_center_iff.mp (hker'' hy) y']
  have hηp : IsPGroup p η.ker := by
    rintro ⟨⟨⟨y, h⟩, hx⟩, hk⟩
    have hh : h = 1 := hk
    have hy : y ∈ ψ''.ker := by
      have hx' : ψ'' y = π h := hx
      rw [MonoidHom.mem_ker, hx', hh, map_one]
    obtain ⟨k, hk'⟩ := hp'' ⟨y, hy⟩
    have hy1 : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk'
    refine ⟨k, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
    · simpa using hy1
    · simp [hh]
  obtain ⟨σ, hσ⟩ := hsec Pb η hη hηker hηp
  set ρ : H →* L' ⧸ N := (MonoidHom.fst _ _).comp (Pb.subtype.comp σ) with hρ
  have hρψ : ∀ h, ψ'' (ρ h) = π h := by
    intro h
    have h1 : ψ'' ((σ h : (L' ⧸ N) × H).1) = π ((σ h : (L' ⧸ N) × H).2) := (σ h).2
    have h2 : (σ h : (L' ⧸ N) × H).2 = h := hσ h
    change ψ'' ((σ h : (L' ⧸ N) × H).1) = _
    rw [h1, h2]
  have hρker : ρ.ker ≤ Subgroup.center H := fun h hh => hπker (by
    rw [MonoidHom.mem_ker, ← hρψ, MonoidHom.mem_ker.mp hh, map_one])
  have hperf'' : commutator (L' ⧸ N) = ⊤ := by
    have : Group.IsPerfect L' := ⟨hperf⟩
    have : Group.IsPerfect (L' ⧸ N) := Group.IsPerfect.ofSurjective hqs
    exact Group.IsPerfect.commutator_eq_top
  have hρs : Function.Surjective ρ := by
    have hdecomp : ∀ y : L' ⧸ N, ∃ h, (ρ h)⁻¹ * y ∈ Subgroup.center (L' ⧸ N) := by
      intro y
      obtain ⟨h, hh⟩ := hπ (ψ'' y)
      refine ⟨h, hker'' ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρψ, hh, inv_mul_cancel]
    have htop : (⊤ : Subgroup (L' ⧸ N)) ≤ ρ.range := by
      rw [← hperf'', _root_.commutator_def, Subgroup.commutator_le]
      intro y₁ _ y₂ _
      obtain ⟨h₁, hh₁⟩ := hdecomp y₁
      obtain ⟨h₂, hh₂⟩ := hdecomp y₂
      refine ⟨⁅h₁, h₂⁆, ?_⟩
      rw [map_commutatorElement]
      have e₁ : y₁ = ρ h₁ * ((ρ h₁)⁻¹ * y₁) := (mul_inv_cancel_left _ _).symm
      have e₂ : y₂ = ρ h₂ * ((ρ h₂)⁻¹ * y₂) := (mul_inv_cancel_left _ _).symm
      rw [e₁, e₂, CFSG.RankThree.PartOne.S15K.commutator_mul_central_left hh₁,
        CFSG.RankThree.PartOne.S15K.commutator_mul_central_right hh₂]
    exact fun y => htop (Subgroup.mem_top y)
  have hHP : Group.IsPerfect H := ⟨hH⟩
  have hρα : ∀ h, ρ (α h) = a'' (ρ h) :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ'' hker'' hHP
      (ρ.comp α.toMonoidHom) (a''.toMonoidHom.comp ρ) (fun u => by
        change ψ'' (ρ (α u)) = ψ'' (a'' (ρ u))
        rw [hρψ, hαπ, ha''ψ, hρψ])
  have hφp : φ ^ p = 1 := eq_one_of_comp_eq hψ fun l => by
    rw [← map_pow_apply (fun x => (hφ x).symm) p l, hap, MulAut.one_apply]
  have hαp : α ^ p = 1 := eq_one_of_map_eq hπker hH fun h => by
    rw [map_pow_apply hαπ p h, hφp, MulAut.one_apply]
  have hα1 : α ≠ 1 := by
    intro h1
    apply ha1
    have hφ1 : φ = 1 := eq_one_of_comp_eq hπ fun h => by
      rw [← hαπ, h1, MulAut.one_apply]
    exact eq_one_of_map_eq hker hperf fun l => by rw [← hφ, hφ1, MulAut.one_apply]
  have hqY : (LargeEvenLayer (ggFix a)).map q = LargeEvenLayer (ggFix a'') :=
    map_largeEvenLayer_ggFix hqs hqker (fun l => (ha''q l).symm)
  have hρY : (LargeEvenLayer (ggFix α)).map ρ = LargeEvenLayer (ggFix a'') :=
    map_largeEvenLayer_ggFix hρs hρker hρα
  have hKq : CFSG.IsQuasisimple (LargeEvenLayer (ggFix a)) :=
    (TableBSymp.isQuasisimple_iff _).mp hcomp.2.2
  have hqKq : CFSG.IsQuasisimple ((LargeEvenLayer (ggFix a)).map q) := by
    refine CFSG.LocalCores.isQuasisimple_map hKq q fun hle => ?_
    obtain ⟨-, -, x, y, hxy⟩ := hKq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    apply hxy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hqker (hle x.2)) y).symm)
  have hXcomp : IsComponentOf (LargeEvenLayer (ggFix α)) (ggFix α) :=
    isComponentOf_largeEvenLayer_of_map ρ hρker _ (by rw [hρY, ← hqY]; exact hqKq)
  set X := LargeEvenLayer (ggFix α) with hX
  have hXperf : ⁅X, X⁆ = X := commutator_largeEvenLayer _
  have hqSX : S.map q ≤ X.map ρ := by
    rw [hρY, ← hqY]
    exact Subgroup.map_mono hSK
  set T : Subgroup H := X ⊓ (S.map q).comap ρ with hT
  have hTX : T ≤ X := inf_le_left
  have hTC : T ≤ Subgroup.centralizer (X : Set H) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    refine (TableBSymp.commute_of_mem_commutator (Y := X) (x := t) (fun y hy => hρker ?_)
      (k := x) (by rw [hXperf]; exact hx)).symm
    obtain ⟨s, hs, hst⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp ht.2)
    have hyK : ρ y ∈ (LargeEvenLayer (ggFix a)).map q := by
      rw [hqY, ← hρY]
      exact ⟨y, hy, rfl⟩
    obtain ⟨k, hk, hky⟩ := hyK
    have hsk : k * s = s * k := Subgroup.mem_centralizer_iff.mp (hSC hs) k hk
    have hc : q s * q k = q k * q s := by rw [← map_mul, ← map_mul, hsk]
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hst, ← hky, hc]
    group
  have hρT : T.map ρ = S.map q := by
    apply le_antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    · intro z hz
      obtain ⟨x, hx, hxz⟩ := hqSX hz
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      show ρ x ∈ S.map q
      rw [hxz]
      exact hz
  have hSqp : IsPGroup p (S.map q) := hSp.map q
  let ρT : T →* S.map q := (ρ.comp T.subtype).codRestrict (S.map q) (fun t => t.2.2)
  have hρTs : Function.Surjective ρT := by
    rintro ⟨z, hz⟩
    rw [← hρT] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  set Q := P.mapSurjective hρTs with hQ
  have hQtop : (Q : Subgroup (S.map q)) = ⊤ := (Q.is_maximal' (hSqp.to_subgroup ⊤) le_top).symm
  have hP'cyc : IsCyclic ((P : Subgroup T).map T.subtype) :=
    hmodel hα1 hαp hXcomp _ (by rintro _ ⟨t, -, rfl⟩; exact hTX t.2)
      (by rintro _ ⟨t, -, rfl⟩; exact hTC t.2) (P.isPGroup'.map T.subtype)
  have hPcyc : IsCyclic (P : Subgroup T) :=
    isCyclic_of_surjective ((P : Subgroup T).equivMapOfInjective T.subtype
      T.subtype_injective).symm (MulEquiv.surjective _)
  have hSqcyc : IsCyclic (S.map q) := by
    have hsurj : Function.Surjective (ρT.comp (P : Subgroup T).subtype) := by
      intro z
      have hz : z ∈ (Q : Subgroup (S.map q)) := by rw [hQtop]; exact Subgroup.mem_top z
      rw [hQ, Sylow.coe_mapSurjective] at hz
      obtain ⟨t, ht, rfl⟩ := hz
      exact ⟨⟨t, ht⟩, rfl⟩
    exact isCyclic_of_surjective _ hsurj
  have hinj : Function.Injective (q.comp S.subtype) := injective_of_isPGroup hker hSp
  have hrange : (q.comp S.subtype).range = S.map q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcycR : IsCyclic (q.comp S.subtype).range := by
    rw [hrange]
    exact hSqcyc
  exact isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm
    (MonoidHom.ofInjective hinj).symm.surjective

theorem ggLayerCenterCyclic_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (e : R ≃* R')
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGLayerCenterCyclic p R' I') :
    GGLayerCenterCyclic p R I := by
  intro L' _ _ ψ hψ hker hperf hZ a ha1 hap hind
  obtain ⟨φ, hφ, hφa⟩ := hind
  have hker' : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) (hker' ▸ hker) hperf hZ a ha1 hap
    ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
  change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
  rw [MulEquiv.symm_apply_apply, hφa]

end CFSG.StandardType

end
