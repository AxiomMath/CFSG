module

public import CFSG.Quasithin.EmptyFaithful.S146D4
public import CFSG.Quasithin.EmptyFaithful.S146D5
public import CFSG.Quasithin.EmptyFaithful.S146D6
public import CFSG.Quasithin.Background.A3Structure312Embed

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section L3Transport

open CFSG.Quasithin.L3Lat

variable {X : Type*} [Group X]

theorem eq_or_top_of_outer_equiv (e : X ≃* Γ) (D P : Subgroup X) (hD : Nat.card D = 8) (hDP : D ≤ P)
    (α : MulAut X) (hαD : ∀ x ∈ D, α x ∈ D) (hαP : ∀ x ∈ P, α x ∈ P)
    (hout : ¬ ∃ k : X, α = MulAut.conj k) : P = D ∨ P = ⊤ := by
  let D' : Subgroup Γ := D.map e.toMonoidHom
  let P' : Subgroup Γ := P.map e.toMonoidHom
  let α' : MulAut Γ := (e.symm.trans α).trans e
  have hα' : ∀ a : Γ, α' a = e (α (e.symm a)) := fun a => rfl
  have hD' : Nat.card D' = 8 := by
    rw [← hD]
    exact Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv
  have hDP' : D' ≤ P' := Subgroup.map_mono hDP
  have hαD' : ∀ x ∈ D', α' x ∈ D' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hα']
    exact Subgroup.mem_map.mpr ⟨α y, hαD y hy, by simp⟩
  have hαP' : ∀ x ∈ P', α' x ∈ P' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hα']
    exact Subgroup.mem_map.mpr ⟨α y, hαP y hy, by simp⟩
  have hout' : ¬ ∃ k : Γ, α' = MulAut.conj k := by
    rintro ⟨k, hk⟩
    apply hout
    refine ⟨e.symm k, ?_⟩
    ext x
    apply e.injective
    have h1 := congrArg (fun f => f (e x)) hk
    simp only [hα', MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1]
    simp [MulAut.conj_apply]
  rcases eq_or_top_of_outer D' P' hD' hDP' α' hαD' hαP' hout' with h | h
  · left
    exact Subgroup.map_injective e.injective h
  · right
    have : P.map e.toMonoidHom = (⊤ : Subgroup X).map e.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ e.surjective]
      exact h
    exact Subgroup.map_injective e.injective this

theorem mem_of_normalizes_equiv (e : X ≃* Γ) (D : Subgroup X) (hD : Nat.card D = 8) (x : X)
    (hx : ∀ d ∈ D, x * d * x⁻¹ ∈ D) : x ∈ D := by
  let D' : Subgroup Γ := D.map e.toMonoidHom
  have hD' : Nat.card D' = 8 := by
    rw [← hD]
    exact Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv
  have h1 : e x ∈ D' := by
    apply mem_of_normalizes D' hD'
    intro d hd
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hd
    exact Subgroup.mem_map.mpr ⟨x * y * x⁻¹, hx y hy, by simp⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
  have : y = x := e.injective hyx
  rw [← this]
  exact hy

end L3Transport

section KBarAut

variable {G : Type} [Group G]

@[expose] def conjAutOn (K : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (K : Set G)) :
    ↥K ≃* ↥K where
  toFun k := ⟨s * k * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs k).mp k.2⟩
  invFun k := ⟨s⁻¹ * k * s, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hs) k).mp k.2
    simpa using this⟩
  left_inv k := Subtype.ext (by simp [mul_assoc])
  right_inv k := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by
    show s * ((a : G) * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹)
    group)

theorem conjAutOn_apply (K : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (K : Set G)) (k : ↥K) :
    ((conjAutOn K s hs k : ↥K) : G) = s * k * s⁻¹ := rfl

theorem map_conjAutOn_pCore (K : Subgroup G) [Finite G] (s : G)
    (hs : s ∈ Subgroup.normalizer (K : Set G)) :
    ((pCoreOf 2 K).subgroupOf K).map (conjAutOn K s hs).toMonoidHom = (pCoreOf 2 K).subgroupOf K := by
  have hs' : s ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := normalizer_le_normalizer_pCoreOf 2 K hs
  have hs'' : s⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := Subgroup.inv_mem _ hs'
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hs' x).mp hx')
  · intro hy
    have hy' : (y : G) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp hy
    refine ⟨(conjAutOn K s hs).symm y, ?_, (conjAutOn K s hs).apply_symm_apply y⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hs'' y).mp hy'
    exact Subgroup.mem_subgroupOf.mpr (show s⁻¹ * (y : G) * s ∈ pCoreOf 2 K by simpa using h1)

@[expose] def kbarAut [Finite G] (K : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (K : Set G)) :
    MulAut (KBar K) :=
  QuotientGroup.congr ((pCoreOf 2 K).subgroupOf K) ((pCoreOf 2 K).subgroupOf K) (conjAutOn K s hs)
    (map_conjAutOn_pCore K s hs)

theorem kbarAut_mk [Finite G] (K : Subgroup G) (s : G) (hs : s ∈ Subgroup.normalizer (K : Set G))
    (k : ↥K) : kbarAut K s hs (QuotientGroup.mk k) = QuotientGroup.mk (conjAutOn K s hs k) :=
  QuotientGroup.congr_mk _ _ _ _ k

end KBarAut

section KImage

variable {G : Type} [Group G] [Finite G]

@[expose] def kbarImage (K X : Subgroup G) : Subgroup (KBar K) :=
  ((X ⊓ K).subgroupOf K).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))

omit [Finite G] in
theorem mk_mem_kbarImage {K X : Subgroup G} (hX : pCoreOf 2 K ≤ X) (k : ↥K) :
    (QuotientGroup.mk k : KBar K) ∈ kbarImage K X ↔ (k : G) ∈ X := by
  constructor
  · rintro ⟨y, hy, hyk⟩
    have h1 : (y : G)⁻¹ * k ∈ pCoreOf 2 K := by
      have := (QuotientGroup.eq (s := (pCoreOf 2 K).subgroupOf K)).mp hyk
      exact Subgroup.mem_subgroupOf.mp this
    have hyX : (y : G) ∈ X := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).1
    have : (k : G) = (y : G) * ((y : G)⁻¹ * k) := by group
    rw [this]
    exact X.mul_mem hyX (hX h1)
  · intro hk
    exact ⟨k, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hk, k.2⟩), rfl⟩

omit [Finite G] in
theorem kbarImage_mono {K X Y : Subgroup G} (h : X ≤ Y) : kbarImage K X ≤ kbarImage K Y := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, Subgroup.mem_subgroupOf.mpr (inf_le_inf_right K h (Subgroup.mem_subgroupOf.mp hy)), rfl⟩

theorem two_pow_eq_eight_of {n b c : ℕ} (hc : c = 168 ∨ c = 360) (h : 2 ^ n * b = c)
    (hb : ¬ 2 ∣ b) : 2 ^ n = 8 := by
  have hn : n ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ c := ⟨2 ^ (n - 4) * b, by
      rw [← h]
      have : 2 ^ n = 2 ^ 4 * 2 ^ (n - 4) := by rw [← pow_add]; congr 1; omega
      rw [this]; ring⟩
    rcases hc with rfl | rfl <;> norm_num at h16
  interval_cases n <;> omega

theorem Setting146.isSylowTwoOf_inf {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) : IsSylowTwoOf (T ⊓ K) K := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  exact A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hTsyl

theorem Setting146.pCoreOf_le_inf {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) : pCoreOf 2 K ≤ T ⊓ K :=
  pCoreOf_two_le_of_isSylowTwoOf (S.isSylowTwoOf_inf hK)

theorem Setting146.card_kbarImage {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hL : KbarIsL3Two K ∨ KbarIsA6 K) : Nat.card (kbarImage K T) = 8 := by
  have hKS : IsSylowTwoOf (T ⊓ K) K := S.isSylowTwoOf_inf hK
  have hOT : pCoreOf 2 K ≤ T ⊓ K := S.pCoreOf_le_inf hK
  set N : Subgroup ↥K := (pCoreOf 2 K).subgroupOf K with hN
  set D : Subgroup ↥K := (T ⊓ K).subgroupOf K with hD
  have hND : N ≤ D := fun x hx => Subgroup.mem_subgroupOf.mpr (hOT (Subgroup.mem_subgroupOf.mp hx))
  have hsurj : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  have hidx : (kbarImage K T).index = D.index := by
    unfold kbarImage
    exact Subgroup.index_map_eq D hsurj (by rw [QuotientGroup.ker_mk']; exact hND)
  have hodd : ¬ 2 ∣ (kbarImage K T).index := by
    rw [hidx]
    exact hKS.2.2
  have hp : IsPGroup 2 (kbarImage K T) := (hKS.2.1.comap_subtype (K := K)).map _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hcard : Nat.card (KBar K) = 168 ∨ Nat.card (KBar K) = 360 := by
    rcases hL with h | h
    · left
      obtain ⟨e⟩ := KbarIsL3Two.nonempty h
      rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field]
      simp [Fin.prod_univ_succ]
    · right
      obtain ⟨e⟩ := KbarIsA6.nonempty h
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
  have hmul := Subgroup.card_mul_index (kbarImage K T)
  rw [hn] at hmul ⊢
  exact two_pow_eq_eight_of hcard hmul hodd

theorem kbarAut_mem_kbarImage {K X : Subgroup G} {s : G} (hs : s ∈ Subgroup.normalizer (K : Set G))
    (hsX : s ∈ X) {x : KBar K} (hx : x ∈ kbarImage K X) : kbarAut K s hs x ∈ kbarImage K X := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hy' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
  show kbarAut K s hs (QuotientGroup.mk y) ∈ kbarImage K X
  rw [kbarAut_mk]
  refine ⟨conjAutOn K s hs y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, (conjAutOn K s hs y).2⟩), rfl⟩
  rw [conjAutOn_apply]
  exact X.mul_mem (X.mul_mem hsX hy'.1) (X.inv_mem hsX)

theorem Setting146.kbarImage_eq_or_top {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) {s : G} (hsT : s ∈ T) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hdyn : KbarNontrivialOnDynkin K s) {B : Subgroup G} (hTB : T ≤ B) :
    kbarImage K B = kbarImage K T ∨ kbarImage K B = ⊤ := by
  have hL : KbarIsL3Two K ∨ KbarIsA6 K := Or.imp (fun h => h.1) (fun h => h.1) hdyn
  have hcard := S.card_kbarImage hK hL
  have hDP : kbarImage K T ≤ kbarImage K B := kbarImage_mono hTB
  have hαD : ∀ x ∈ kbarImage K T, kbarAut K s hsK x ∈ kbarImage K T := fun x hx =>
    kbarAut_mem_kbarImage hsK hsT hx
  have hαP : ∀ x ∈ kbarImage K B, kbarAut K s hsK x ∈ kbarImage K B := fun x hx =>
    kbarAut_mem_kbarImage hsK (hTB hsT) hx
  rcases hdyn with ⟨hL3, hout⟩ | ⟨hA6, x, hxK, hx3, hxn, hxcls⟩
  · obtain ⟨e⟩ := KbarIsL3Two.nonempty hL3
    refine eq_or_top_of_outer_equiv e (kbarImage K T) (kbarImage K B) hcard hDP (kbarAut K s hsK)
      hαD hαP ?_
    rintro ⟨kb, hkb⟩
    obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective kb
    obtain ⟨x, hxK, hx⟩ := hout k₀ k₀.2
    apply hx
    have hQ : ∀ y ∈ K, ∀ q ∈ pCoreOf 2 K, y * q * y⁻¹ ∈ pCoreOf 2 K := fun y hy q hq =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hy) q).mp hq
    have hx'K : (k₀ : G)⁻¹ * x * k₀ ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k₀.2) hxK) k₀.2
    let x' : ↥K := ⟨(k₀ : G)⁻¹ * x * k₀, hx'K⟩
    have hx'eq : x' = k₀⁻¹ * ⟨x, hxK⟩ * k₀ := Subtype.ext rfl
    have h1 : kbarAut K s hsK (QuotientGroup.mk x') = QuotientGroup.mk ⟨x, hxK⟩ := by
      have h0 := congrArg (fun f => f (QuotientGroup.mk x' : KBar K)) hkb
      simp only [MulAut.conj_apply] at h0
      rw [h0, hx'eq]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      group
    rw [kbarAut_mk] at h1
    have h2 := (QuotientGroup.eq (s := (pCoreOf 2 K).subgroupOf K)).mp h1
    have h3 : (s * ((k₀ : G)⁻¹ * x * k₀) * s⁻¹)⁻¹ * x ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h2
    have h4 := Subgroup.inv_mem _ h3
    have h5 := hQ x hxK _ h4
    have e1 : x * ((s * ((k₀ : G)⁻¹ * x * k₀) * s⁻¹)⁻¹ * x)⁻¹ * x⁻¹ = ⁅s * (k₀ : G)⁻¹, x⁆ := by
      rw [commutatorElement_def]
      group
    rw [← e1]
    exact h5
  · obtain ⟨e⟩ := KbarIsA6.nonempty hA6
    refine A6Lat.eq_or_top_of_fuse e (kbarImage K T) (kbarImage K B) hcard hDP (kbarAut K s hsK) hαP ?_
    refine ⟨QuotientGroup.mk ⟨x, hxK⟩, ?_, ?_, fun kb hkb => ?_⟩
    · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa [pow_succ, mul_assoc] using hx3)
    · intro h
      exact hxn (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h))
    · obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective kb
      rw [kbarAut_mk] at hkb
      have h3 : (QuotientGroup.mk (k * ⟨x, hxK⟩ * k⁻¹) : KBar K) =
          QuotientGroup.mk (conjAutOn K s hsK ⟨x, hxK⟩) := by
        rw [← hkb]
        simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h2 := (QuotientGroup.eq (s := (pCoreOf 2 K).subgroupOf K)).mp h3
      exact hxcls k k.2 (Subgroup.mem_subgroupOf.mp h2)

theorem Setting146.inf_le_or_le {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) {s : G} (hsT : s ∈ T) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hdyn : KbarNontrivialOnDynkin K s) {B : Subgroup G} (hTB : T ≤ B) : K ⊓ B ≤ T ∨ K ≤ B := by
  have hOT : pCoreOf 2 K ≤ T := (S.pCoreOf_le_inf hK).trans inf_le_left
  have hOB : pCoreOf 2 K ≤ B := hOT.trans hTB
  rcases S.kbarImage_eq_or_top hK hsT hsK hdyn hTB with h | h
  · left
    intro x hx
    have h1 : (QuotientGroup.mk ⟨x, hx.1⟩ : KBar K) ∈ kbarImage K B :=
      (mk_mem_kbarImage hOB _).mpr hx.2
    rw [h] at h1
    exact (mk_mem_kbarImage hOT _).mp h1
  · right
    intro x hx
    have h1 : (QuotientGroup.mk ⟨x, hx⟩ : KBar K) ∈ kbarImage K B := by
      rw [h]
      exact Subgroup.mem_top _
    exact (mk_mem_kbarImage hOB _).mp h1

theorem Setting146.mem_of_normalizes {T M : Subgroup G} (S : Setting146 G T M) {K : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hL3 : KbarIsL3Two K) {k : G} (hk : k ∈ K)
    (hn : ∀ d ∈ T ⊓ K, k * d * k⁻¹ ∈ T) : k ∈ T := by
  obtain ⟨e⟩ := KbarIsL3Two.nonempty hL3
  have hcard := S.card_kbarImage hK (Or.inl hL3)
  have hOT : pCoreOf 2 K ≤ T := (S.pCoreOf_le_inf hK).trans inf_le_left
  have h1 : (QuotientGroup.mk ⟨k, hk⟩ : KBar K) ∈ kbarImage K T := by
    refine mem_of_normalizes_equiv e (kbarImage K T) hcard _ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)
    have : (QuotientGroup.mk ⟨k, hk⟩ : KBar K) * QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) y *
        (QuotientGroup.mk ⟨k, hk⟩ : KBar K)⁻¹ = QuotientGroup.mk (⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹ : ↥K) := by
      simp
    rw [this, mk_mem_kbarImage hOT]
    exact hn y ⟨hy'.1, y.2⟩
  exact (mk_mem_kbarImage hOT _).mp h1

end KImage

end CFSG.Quasithin
