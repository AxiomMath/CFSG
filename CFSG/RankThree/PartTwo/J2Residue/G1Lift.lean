module

public import CFSG.RankThree.PartTwo.J2Residue.KFacts
public import CFSG.RankThree.PartTwo.J2Residue.Config
import CFSG.GroupTheory.CardMapInfKer
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG CFSG.Blueprint.NativeSporadic
open scoped Pointwise

private lemma map_conj_subtype {G : Type} [Group G] {L : Subgroup G}
    (T : Subgroup ↥L) (n : ↥L) :
    (T.map (MulAut.conj n).toMonoidHom).map L.subtype =
      (T.map L.subtype).map (MulAut.conj (n : G)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma injective_of_disjoint_ker {L' J : Type} [Group L'] [Group J]
    {f : L' →* J} {S P : Subgroup L'} (hker : f.ker = P) (hdisj : Disjoint S P) :
    ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y := by
  intro x hx y hy hxy
  have hmem : x * y⁻¹ ∈ S ⊓ f.ker := by
    refine ⟨S.mul_mem hx (S.inv_mem hy), ?_⟩
    change f (x * y⁻¹) = 1
    simp [map_mul, map_inv, hxy]
  rw [hker, hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

private lemma mem_map_iff_mem_of_injOn {L' J : Type} [Group L'] [Group J]
    {f : L' →* J} {S D : Subgroup L'} (hD : D ≤ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    {x : L'} (hx : x ∈ S) : f x ∈ D.map f ↔ x ∈ D := by
  constructor
  · rintro ⟨d, hd, hdx⟩
    exact (hinj d (hD hd) x hx hdx) ▸ hd
  · intro hx''
    exact Subgroup.mem_map_of_mem f hx''

private lemma map_lt_map_of_lt_of_injOn {L' J : Type} [Group L'] [Group J]
    {f : L' →* J} {S H K : Subgroup L'} (hK : K ≤ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    (hHK : H < K) : H.map f < K.map f := by
  have hle : H ≤ K := hHK.le
  refine lt_of_le_of_ne (Subgroup.map_mono hle) ?_
  intro heq
  apply hHK.ne
  refine le_antisymm hle ?_
  intro k hk
  have hfk : f k ∈ H.map f := by
    rw [heq]
    exact Subgroup.mem_map_of_mem f hk
  rcases Subgroup.mem_map.mp hfk with ⟨h, hh, hhk⟩
  have hhS : h ∈ S := hle.trans hK hh
  have hkS : k ∈ S := hK hk
  exact (hinj h hhS k hkS hhk) ▸ hh

private lemma isSylowOf_of_sup_eq {L' : Type} [Group L'] [Finite L']
    {P S K : Subgroup L'} [P.Normal] (hK : K = S ⊔ P)
    (hP2 : IsPGroup 2 P) (hS3 : IsPGroup 3 S) (hdisj : Disjoint S P) :
    CFSG.ABGLocalTools.IsSylowOf 3 S K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨by rw [hK]; exact le_sup_left, hS3, ?_⟩
  have hrel : S.relIndex K = Nat.card P := by
    rw [hK, sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal P S]
    have h := Subgroup.relIndex_mul_card S P
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one] at h
    exact h
  rw [hrel]
  obtain ⟨n, hn⟩ := hP2.exists_card_eq
  rw [hn]
  exact fun hdvd => absurd ((by norm_num : Nat.Prime 3).dvd_of_dvd_pow hdvd) (by norm_num)

private lemma mem_normalizer_of_map_mem_normalizer {L' J : Type} [Group L'] [Group J]
    {f : L' →* J} {S D : Subgroup L'} (hD : D ≤ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y)
    {n' : L'} {nbar : J} (hnS : n' ∈ Subgroup.normalizer (S : Set L'))
    (hfn : f n' = nbar) (hnbarD : nbar ∈ Subgroup.normalizer (D.map f : Set J)) :
    n' ∈ Subgroup.normalizer (D : Set L') := by
  rw [Subgroup.mem_normalizer_iff] at hnbarD ⊢
  intro s
  have hsS' : s ∈ S ↔ n' * s * n'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hnS) s
  constructor
  · intro hs
    have hsS : s ∈ S := hD hs
    have hnsS : n' * s * n'⁻¹ ∈ S := (hsS').mp hsS
    have hmap : f (n' * s * n'⁻¹) ∈ D.map f := by
      have h := (hnbarD (f s)).mp (Subgroup.mem_map_of_mem f hs)
      simpa [map_mul, hfn] using h
    exact (mem_map_iff_mem_of_injOn hD hinj hnsS).mp hmap
  · intro hns
    have hnsS : n' * s * n'⁻¹ ∈ S := hD hns
    have hsS : s ∈ S := (hsS').mpr hnsS
    have hmap : f s ∈ D.map f := by
      have hDmem : f (n' * s * n'⁻¹) ∈ D.map f := Subgroup.mem_map_of_mem f hns
      have h := (hnbarD (f s)).mpr (by simpa [map_mul, hfn] using hDmem)
      simpa [map_mul, hfn] using h
    exact (mem_map_iff_mem_of_injOn hD hinj hsS).mp hmap

private lemma exists_P_conj_map
    {L' J : Type} [Group L'] [Finite L'] [Group J]
    (f : L' →* J) (P S : Subgroup L') [P.Normal]
    (hker : f.ker = P) (hP2 : IsPGroup 2 P) (hS3 : IsPGroup 3 S)
    (hdisj : Disjoint S P)
    {x : L'} {nbar : J} (hnbar : nbar ∈ Subgroup.normalizer (S.map f : Set J))
    (hx : f x = nbar) :
    ∃ p ∈ P, S.map (MulAut.conj x).toMonoidHom = S.map (MulAut.conj p).toMonoidHom := by
  classical
  let K : Subgroup L' := S ⊔ P
  let A : Subgroup L' := S.map (MulAut.conj x).toMonoidHom
  have hSP : S ⊓ P = ⊥ := hdisj.eq_bot
  have hAK : A ≤ K := by
    rintro y ⟨s, hs, rfl⟩
    have hfmem : f (x * s * x⁻¹) ∈ S.map f := by
      have hsmap : f s ∈ S.map f := Subgroup.mem_map_of_mem f hs
      have hh := (Subgroup.mem_normalizer_iff.mp hnbar (f s)).mp hsmap
      simpa [map_mul, map_inv, hx] using hh
    have hcomap : x * s * x⁻¹ ∈ (S.map f).comap f := hfmem
    rw [Subgroup.comap_map_eq, hker] at hcomap
    exact hcomap
  have hA3 : IsPGroup 3 A := hS3.map _
  have hPmap : P.map (MulAut.conj x).toMonoidHom = P := Subgroup.Normal.map_conj_eq P x
  have hdisjA : Disjoint A P := by
    have hinf : A ⊓ P = ⊥ := by
      rw [← hPmap, ← Subgroup.map_inf_eq S P _ (MulAut.conj x).injective, hSP, Subgroup.map_bot]
    exact disjoint_iff.mpr hinf
  have hsupA : A ⊔ P = K := by
    have hmapK : K.map (MulAut.conj x).toMonoidHom = A ⊔ P := by
      rw [show K = S ⊔ P from rfl, Subgroup.map_sup, hPmap]
    have hle : K.map (MulAut.conj x).toMonoidHom ≤ K := by
      rw [hmapK]
      exact sup_le hAK le_sup_right
    have hcard : Nat.card (K.map (MulAut.conj x).toMonoidHom) = Nat.card K :=
      Subgroup.card_map_of_injective (MulAut.conj x).injective
    have hEq : K.map (MulAut.conj x).toMonoidHom = K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])
    rw [← hmapK, hEq]
  have hS_sylow : CFSG.ABGLocalTools.IsSylowOf 3 S K :=
    isSylowOf_of_sup_eq rfl hP2 hS3 hdisj
  have hA_sylow : CFSG.ABGLocalTools.IsSylowOf 3 A K :=
    isSylowOf_of_sup_eq hsupA.symm hP2 hA3 hdisjA
  obtain ⟨k, hkK, hconj⟩ :=
    CFSG.ClassicalInvolution.GlaubermanAut.isSylowOf_exists_conj hS_sylow hA_sylow
  have hmul : (k : L') ∈ (P : Set L') * (S : Set L') := by
    have h : (k : L') ∈ ((P ⊔ S : Subgroup L') : Set L') := by
      simpa [K, sup_comm] using hkK
    simpa [Subgroup.normal_mul] using h
  obtain ⟨p, hp, s₀, hs₀, hk_eq⟩ := Set.mem_mul.mp hmul
  have hk_eq' : (k : L') = p * s₀ := hk_eq.symm
  refine ⟨p, hp, ?_⟩
  show A = S.map (MulAut.conj p).toMonoidHom
  ext y
  constructor
  · intro hy
    have hks : k⁻¹ * y * k ∈ S := (hconj y).mp hy
    refine Subgroup.mem_map.mpr ⟨s₀ * (k⁻¹ * y * k) * s₀⁻¹,
      S.mul_mem (S.mul_mem hs₀ hks) (S.inv_mem hs₀), ?_⟩
    change p * (s₀ * (k⁻¹ * y * k) * s₀⁻¹) * p⁻¹ = y
    rw [hk_eq']
    group
  · rintro ⟨t, ht, rfl⟩
    have hs : s₀⁻¹ * t * s₀ ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs₀) ht) hs₀
    refine (hconj (p * t * p⁻¹)).mpr ?_
    rw [hk_eq']
    convert hs using 1
    group

private lemma exists_normalizer_lift
    {L' J : Type} [Group L'] [Finite L'] [Group J]
    (f : L' →* J) (P S : Subgroup L') [P.Normal]
    (hker : f.ker = P) (hP2 : IsPGroup 2 P) (hS3 : IsPGroup 3 S)
    (hdisj : Disjoint S P)
    {x : L'} {nbar : J} (hnbar : nbar ∈ Subgroup.normalizer (S.map f : Set J))
    (hx : f x = nbar) :
    ∃ n' ∈ Subgroup.normalizer (S : Set L'), f n' = nbar := by
  obtain ⟨p, hp, hA_p⟩ := exists_P_conj_map f P S hker hP2 hS3 hdisj hnbar hx
  refine ⟨p⁻¹ * x, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have hxA : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hs
      rw [hA_p] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨t, ht, hpt⟩
      change p * t * p⁻¹ = x * s * x⁻¹ at hpt
      convert ht using 1
      rw [show p⁻¹ * x * s * (p⁻¹ * x)⁻¹ = p⁻¹ * (x * s * x⁻¹) * p by group, ← hpt]
      group
    · intro hs
      have hs' : p⁻¹ * x * s * x⁻¹ * p ∈ S := by
        convert hs using 1
        group
      have hxA : x * s * x⁻¹ ∈ S.map (MulAut.conj x).toMonoidHom := by
        rw [hA_p]
        refine Subgroup.mem_map.mpr ⟨p⁻¹ * x * s * x⁻¹ * p, hs', ?_⟩
        change p * (p⁻¹ * x * s * x⁻¹ * p) * p⁻¹ = x * s * x⁻¹
        group
      rcases Subgroup.mem_map.mp hxA with ⟨t, ht, hxt⟩
      change x * t * x⁻¹ = x * s * x⁻¹ at hxt
      have hts : t = s := by
        have h := congrArg (fun z => x⁻¹ * z * x) hxt
        simpa [mul_assoc] using h
      exact hts ▸ ht
  · rw [map_mul, map_inv]
    have hfp : f p = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hp
    rw [hfp, hx]
    simp

theorem J2Config.g1 (hG1 : KG1) {G : Type} [Group G] [Finite G] {L LB : Subgroup G} {d : G}
    (h : J2Config L d LB) {S : Subgroup G} (hSLB : S ≤ LB) (hS : Nat.card S = 27)
    (hdS : d ∈ S) :
    (∀ T₁ T₂ : Subgroup G, Subgroup.zpowers d < T₁ → T₁ < S → Subgroup.zpowers d < T₂ →
      T₂ < S → ∃ n ∈ L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G),
        n ∈ Subgroup.normalizer (S : Set G) ∧ T₁.map (MulAut.conj n).toMonoidHom = T₂) ∧
    ∃ n ∈ L ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G),
      n ∈ Subgroup.normalizer (S : Set G) ∧ ∀ s ∈ S, n * s * n⁻¹ * s ∈ Subgroup.zpowers d := by
  classical
  have hLB_le_L : LB ≤ L := by
    rw [h.lB_eq]
    exact (Subgroup.map_subtype_le (CFSG.perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).trans
      inf_le_left
  have hSL : S ≤ L := hSLB.trans hLB_le_L
  have hLB_le_C : LB ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [h.lB_eq]
    exact (Subgroup.map_subtype_le (CFSG.perfectResidual ↥(L ⊓ Subgroup.centralizer ({d} : Set G)))).trans
      inf_le_right
  have hSC : S ≤ Subgroup.centralizer ({d} : Set G) := hSLB.trans hLB_le_C
  let P : Subgroup ↥L := CFSG.pCore 2 ↥L
  let φ : ↥L ⧸ P ≃* J2 := h.j2.some
  let f : ↥L →* J2 := φ.toMonoidHom.comp (QuotientGroup.mk' P)
  let S' : Subgroup ↥L := S.subgroupOf L
  let d' : ↥L := ⟨d, h.mem_d⟩
  have hSmap : S'.map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSL
  have hcardS' : Nat.card S' = 27 := by
    rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective, hSmap, hS]
  have hS'3 : IsPGroup 3 S' := IsPGroup.of_card (n := 3) (by rw [hcardS']; norm_num)
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hdisj : Disjoint S' P := IsPGroup.disjoint_of_ne 3 2 (by norm_num) S' P hS'3 hP2
  have hker : f.ker = P := by
    ext x
    constructor
    · intro hx
      have hx' : (QuotientGroup.mk' P x) = 1 := by
        apply φ.injective
        simpa [f] using hx
      simpa [QuotientGroup.eq_one_iff] using hx'
    · intro hx
      simp [f, hx]
  have hinj : ∀ x ∈ S', ∀ y ∈ S', f x = f y → x = y :=
    injective_of_disjoint_ker hker hdisj
  have hfsurj : Function.Surjective f := φ.surjective.comp (QuotientGroup.mk'_surjective P)
  have hd'S : d' ∈ S' := Subgroup.mem_subgroupOf.mpr hdS
  have horder : orderOf d' = 3 := by
    rw [Subgroup.orderOf_mk]
    exact h.orderOf_d
  have hcardmap : Nat.card (S'.map f) = 27 := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot f (by rw [hker]; exact hdisj.eq_bot), hcardS']
  have hfdmem : f d' ∈ S'.map f := Subgroup.mem_map_of_mem f hd'S
  have hfdne : f d' ≠ 1 := by
    intro h1
    have hd1 : d' = 1 := hinj d' hd'S 1 (S'.one_mem) (by simpa using h1)
    have hord1 : orderOf d' = 1 := by rw [hd1]; simp
    rw [horder] at hord1
    norm_num at hord1
  have hcentral : S'.map f ≤ Subgroup.centralizer ({f d'} : Set J2) := by
    rintro y ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hcommG : (s : G) * d = d * (s : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hSC hsS)
    have hcommL : s * d' = d' * s := by
      apply Subtype.ext
      simpa [d'] using hcommG
    have hh := congrArg f hcommL
    simpa [map_mul] using hh
  obtain ⟨htrans, hinv⟩ := hG1 (f d') (S'.map f) hcardmap hfdne hfdmem hcentral
  have hD' : Subgroup.zpowers d' ≤ S' := Subgroup.zpowers_le.mpr hd'S
  have hDmap : Subgroup.zpowers d' = (Subgroup.zpowers d).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr h.mem_d)]
    rfl
  have hDmapG : (Subgroup.zpowers d').map L.subtype = Subgroup.zpowers d := by
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨?_, ?_⟩
  · intro T₁ T₂ hT₁ hT₁S hT₂ hT₂S
    have hT₁L : T₁ ≤ L := hT₁S.le.trans hSL
    have hT₂L : T₂ ≤ L := hT₂S.le.trans hSL
    let T₁' : Subgroup ↥L := T₁.subgroupOf L
    let T₂' : Subgroup ↥L := T₂.subgroupOf L
    have hT₁map : T₁'.map L.subtype = T₁ := Subgroup.map_subgroupOf_eq_of_le hT₁L
    have hT₂map : T₂'.map L.subtype = T₂ := Subgroup.map_subgroupOf_eq_of_le hT₂L
    have hT₁'S' : T₁' ≤ S' := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hT₁S.le (Subgroup.mem_subgroupOf.mp hx))
    have hT₂'S' : T₂' ≤ S' := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hT₂S.le (Subgroup.mem_subgroupOf.mp hx))
    have hlt1 : Subgroup.zpowers d' < T₁' := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := L.subtype) L.subtype_injective]
      rw [hDmap, Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr h.mem_d), hT₁map]
      exact hT₁
    have hlt1S : T₁' < S' := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := L.subtype) L.subtype_injective]
      rw [hT₁map, hSmap]
      exact hT₁S
    have hlt2 : Subgroup.zpowers d' < T₂' := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := L.subtype) L.subtype_injective]
      rw [hDmap, Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr h.mem_d), hT₂map]
      exact hT₂
    have hlt2S : T₂' < S' := by
      rw [← Subgroup.map_lt_map_iff_of_injective (f := L.subtype) L.subtype_injective]
      rw [hT₂map, hSmap]
      exact hT₂S
    have hJ1 : Subgroup.zpowers (f d') < T₁'.map f := by
      have h := map_lt_map_of_lt_of_injOn (f := f) (S := S') (H := Subgroup.zpowers d')
        (K := T₁') hT₁'S' hinj hlt1
      rwa [MonoidHom.map_zpowers] at h
    have hJ1S : T₁'.map f < S'.map f :=
      map_lt_map_of_lt_of_injOn (f := f) (S := S') (H := T₁') (K := S') le_rfl hinj hlt1S
    have hJ2 : Subgroup.zpowers (f d') < T₂'.map f := by
      have h := map_lt_map_of_lt_of_injOn (f := f) (S := S') (H := Subgroup.zpowers d')
        (K := T₂') hT₂'S' hinj hlt2
      rwa [MonoidHom.map_zpowers] at h
    have hJ2S : T₂'.map f < S'.map f :=
      map_lt_map_of_lt_of_injOn (f := f) (S := S') (H := T₂') (K := S') le_rfl hinj hlt2S
    obtain ⟨nbar, hnbar_mem, hnbar_conj⟩ :=
      htrans (T₁'.map f) (T₂'.map f) hJ1 hJ1S hJ2 hJ2S
    have hnbarS : nbar ∈ Subgroup.normalizer (S'.map f : Set J2) :=
      (Subgroup.mem_inf.mp hnbar_mem).1
    have hnbarD : nbar ∈ Subgroup.normalizer (Subgroup.zpowers (f d') : Set J2) :=
      (Subgroup.mem_inf.mp hnbar_mem).2
    obtain ⟨x, hx⟩ := hfsurj nbar
    obtain ⟨n', hn'S, hn'f⟩ := exists_normalizer_lift f P S' hker hP2 hS'3 hdisj hnbarS hx
    have hn'D : n' ∈ Subgroup.normalizer (Subgroup.zpowers d' : Set ↥L) :=
      mem_normalizer_of_map_mem_normalizer hD' hinj hn'S hn'f (by rwa [MonoidHom.map_zpowers])
    have hnS : (n' : G) ∈ Subgroup.normalizer (S : Set G) := by
      have hmem : (n' : G) ∈ (Subgroup.normalizer (S' : Set ↥L)).map L.subtype :=
        ⟨n', hn'S, rfl⟩
      simpa [hSmap] using Subgroup.le_normalizer_map L.subtype hmem
    have hnD : (n' : G) ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      have hmem : (n' : G) ∈ (Subgroup.normalizer (Subgroup.zpowers d' : Set ↥L)).map L.subtype :=
        ⟨n', hn'D, rfl⟩
      simpa [hDmapG] using Subgroup.le_normalizer_map L.subtype hmem
    have hn'le : T₁'.map (MulAut.conj n').toMonoidHom ≤ S' := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨t, ht, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hn'S t).mp (hT₁'S' ht)
    have himg : (T₁'.map (MulAut.conj n').toMonoidHom).map f = T₂'.map f := by
      rw [Subgroup.map_map]
      have hcomp : f.comp (MulAut.conj n').toMonoidHom =
          (MulAut.conj nbar).toMonoidHom.comp f := by
        ext y
        simp [MulAut.conj_apply, map_mul, hn'f]
      rw [hcomp, ← Subgroup.map_map]
      exact hnbar_conj
    have hconjT' : T₁'.map (MulAut.conj n').toMonoidHom = T₂' := by
      apply le_antisymm
      · intro y hy
        have hyS : y ∈ S' := hn'le hy
        have hfy : f y ∈ T₂'.map f := by
          rw [← himg]
          exact Subgroup.mem_map_of_mem f hy
        rcases Subgroup.mem_map.mp hfy with ⟨t, ht, hty⟩
        exact (hinj t (hT₂'S' ht) y hyS hty) ▸ ht
      · intro y hy
        have hyS : y ∈ S' := hT₂'S' hy
        have hfy : f y ∈ (T₁'.map (MulAut.conj n').toMonoidHom).map f := by
          rw [himg]
          exact Subgroup.mem_map_of_mem f hy
        rcases Subgroup.mem_map.mp hfy with ⟨t, ht, hty⟩
        exact (hinj t (hn'le ht) y hyS hty) ▸ ht
    have hconjT : T₁.map (MulAut.conj (n' : G)).toMonoidHom = T₂ := by
      calc T₁.map (MulAut.conj (n' : G)).toMonoidHom
          = (T₁'.map (MulAut.conj n').toMonoidHom).map L.subtype := by
            rw [← hT₁map]
            exact (map_conj_subtype T₁' n').symm
        _ = T₂'.map L.subtype := by rw [hconjT']
        _ = T₂ := hT₂map
    exact ⟨(n' : G), ⟨n'.2, hnD⟩, hnS, hconjT⟩
  · obtain ⟨nbar, hnbar_mem, hnbar_all⟩ := hinv
    have hnbarS : nbar ∈ Subgroup.normalizer (S'.map f : Set J2) :=
      (Subgroup.mem_inf.mp hnbar_mem).1
    have hnbarD : nbar ∈ Subgroup.normalizer (Subgroup.zpowers (f d') : Set J2) :=
      (Subgroup.mem_inf.mp hnbar_mem).2
    obtain ⟨x, hx⟩ := hfsurj nbar
    obtain ⟨n', hn'S, hn'f⟩ := exists_normalizer_lift f P S' hker hP2 hS'3 hdisj hnbarS hx
    have hn'D : n' ∈ Subgroup.normalizer (Subgroup.zpowers d' : Set ↥L) :=
      mem_normalizer_of_map_mem_normalizer hD' hinj hn'S hn'f (by rwa [MonoidHom.map_zpowers])
    have hnS : (n' : G) ∈ Subgroup.normalizer (S : Set G) := by
      have hmem : (n' : G) ∈ (Subgroup.normalizer (S' : Set ↥L)).map L.subtype :=
        ⟨n', hn'S, rfl⟩
      simpa [hSmap] using Subgroup.le_normalizer_map L.subtype hmem
    have hnD : (n' : G) ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
      have hmem : (n' : G) ∈ (Subgroup.normalizer (Subgroup.zpowers d' : Set ↥L)).map L.subtype :=
        ⟨n', hn'D, rfl⟩
      simpa [hDmapG] using Subgroup.le_normalizer_map L.subtype hmem
    have hall : ∀ s ∈ S, (n' : G) * s * (n' : G)⁻¹ * s ∈ Subgroup.zpowers d := by
      intro s hs
      let s' : ↥L := ⟨s, hSL hs⟩
      have hs' : s' ∈ S' := Subgroup.mem_subgroupOf.mpr hs
      have hns'S : n' * s' * n'⁻¹ * s' ∈ S' :=
        S'.mul_mem ((Subgroup.mem_normalizer_iff.mp hn'S s').mp hs') hs'
      have hmapmem : f (n' * s' * n'⁻¹ * s') ∈ Subgroup.zpowers (f d') := by
        have hsmap : f s' ∈ S'.map f := Subgroup.mem_map_of_mem f hs'
        have hh := hnbar_all (f s') hsmap
        simpa [map_mul, map_inv, hn'f] using hh
      rw [← MonoidHom.map_zpowers f d'] at hmapmem
      have hzmem : n' * s' * n'⁻¹ * s' ∈ Subgroup.zpowers d' :=
        (mem_map_iff_mem_of_injOn hD' hinj hns'S).mp hmapmem
      have hval : ((n' * s' * n'⁻¹ * s' : ↥L) : G) ∈ Subgroup.zpowers d := by
        have hm := Subgroup.mem_map_of_mem L.subtype hzmem
        rwa [hDmapG] at hm
      simpa [s'] using hval
    exact ⟨(n' : G), ⟨n'.2, hnD⟩, hnS, hall⟩

end CFSG.RankThree.PartTwo.J2Residue
