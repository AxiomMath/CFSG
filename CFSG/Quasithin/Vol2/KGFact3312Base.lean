module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312KG
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalStrong

public section

namespace CFSG.Quasithin.H13.KG3312

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open scoped Pointwise

variable {Q : Type} [Group Q]

theorem conj_map (d : MulAut Q) (x : Q) : MulAut.conj (d x) = d * MulAut.conj x * d⁻¹ := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem conj_injective (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [← hZ]
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have h := congrArg (fun e : MulAut Q => e y) (MonoidHom.mem_ker.mp hx)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h
  calc y * x = x * y * x⁻¹ * x := by rw [h]
    _ = x * y := by group

theorem mem_normalizer_of_conj_mem {B : Subgroup Q} {t : Q}
    (h : MulAut.conj t ∈ MulAction.stabilizer (MulAut Q) B) :
    t ∈ Subgroup.normalizer (B : Set Q) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (mem_stabilizer_subgroup_iff.mp h)

theorem comap_conj_le_normalizer {S : Subgroup (MulAut Q)} {B : Subgroup Q}
    (hSB : S ≤ MulAction.stabilizer (MulAut Q) B) :
    S.comap (MulAut.conj : Q →* MulAut Q) ≤ Subgroup.normalizer (B : Set Q) :=
  fun _ ht => mem_normalizer_of_conj_mem (hSB ht)

theorem le_stabilizer_smul {S : Subgroup (MulAut Q)} {B : Subgroup Q}
    (hSB : S ≤ MulAction.stabilizer (MulAut Q) B) {d : MulAut Q}
    (hd : d ∈ Subgroup.normalizer (S : Set (MulAut Q))) :
    S ≤ MulAction.stabilizer (MulAut Q) (d • B) := by
  intro s hs
  have h1 : d⁻¹ * s * d ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) s).mp hs
    simpa using this
  have h2 : (d⁻¹ * s * d) • B = B := MulAction.mem_stabilizer_iff.mp (hSB h1)
  rw [MulAction.mem_stabilizer_iff]
  calc s • d • B = d • ((d⁻¹ * s * d) • B) := by
        rw [smul_smul, smul_smul]
        congr 1
        group
    _ = d • B := by rw [h2]

theorem map_comap_conj {S : Subgroup (MulAut Q)} {d : MulAut Q}
    (hd : d ∈ Subgroup.normalizer (S : Set (MulAut Q))) :
    (S.comap (MulAut.conj : Q →* MulAut Q)).map d.toMonoidHom =
      S.comap (MulAut.conj : Q →* MulAut Q) := by
  refine le_antisymm ?_ fun y hy => ⟨d⁻¹ y, ?_, by simp⟩
  · rintro _ ⟨x, hx, rfl⟩
    show MulAut.conj (d x) ∈ S
    rw [conj_map]
    exact (Subgroup.mem_normalizer_iff.mp hd _).mp hx
  · show MulAut.conj (d⁻¹ y) ∈ S
    rw [conj_map]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hd) _).mp hy
    simpa using this

theorem index_comap_conj_odd [Finite Q] {A S : Subgroup (MulAut Q)}
    (hA : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) :
    ¬ 2 ∣ (S.comap (MulAut.conj : Q →* MulAut Q)).index := by
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun e : MulAut Q => (e : Q → Q)) fun _ _ h => MulEquiv.ext (congrFun h)
  set I : Subgroup (MulAut Q) := (MulAut.conj : Q →* MulAut Q).range with hI
  have hnorm : A ≤ Subgroup.normalizer (I : Set (MulAut Q)) := by
    have : I.Normal := inner_normal Q
    rw [Subgroup.normalizer_eq_top_iff.mpr this]
    exact le_top
  have hSI : IsSylowTwoOf (S ⊓ I) I := A4.isSylowTwoOf_inf_normal hS hA hnorm
  let φ : Q →* ↥I := (MulAut.conj : Q →* MulAut Q).rangeRestrict
  have hcomap : S.comap (MulAut.conj : Q →* MulAut Q) = ((S ⊓ I).subgroupOf I).comap φ := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨h, x, rfl⟩, fun h => h.1⟩
  rw [hcomap, Subgroup.index_comap_of_surjective _ (MonoidHom.rangeRestrict_surjective _)]
  exact hSI.2.2

theorem isSylowTwoOf_comap_conj [Finite Q]
    (hinj : Function.Injective (MulAut.conj : Q →* MulAut Q)) {A S : Subgroup (MulAut Q)}
    (hA : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) :
    IsSylowTwoOf (S.comap (MulAut.conj : Q →* MulAut Q)) ⊤ :=
  K1.isSylowTwoOf_top_iff.mpr
    ⟨hS.2.1.comap_of_injective _ hinj, index_comap_conj_odd hA hS⟩

theorem exists_sylow_comap_conj [Finite Q] {A S : Subgroup (MulAut Q)}
    (hA : (MulAut.conj : Q →* MulAut Q).range ≤ A) (hS : IsSylowTwoOf S A) :
    ∃ U : Subgroup Q, IsSylowTwoOf U ⊤ ∧ U ≤ S.comap (MulAut.conj : Q →* MulAut Q) ∧
      ∀ d ∈ Subgroup.normalizer (S : Set (MulAut Q)), U.map d.toMonoidHom = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup Q := S.comap (MulAut.conj : Q →* MulAut Q) with hT
  let ψ : ↥T →* ↥S := ((MulAut.conj : Q →* MulAut Q).comp T.subtype).codRestrict S
    fun x => x.2
  have hker : ψ.ker ≤ Subgroup.center ↥T := by
    intro x hx
    have h1 : MulAut.conj (x : Q) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    have h2 := congrArg (fun e : MulAut Q => e (y : Q)) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    have h3 : (x : Q) * y = y * x := by
      calc (x : Q) * y = (x * y * (x : Q)⁻¹) * x := by group
        _ = y * x := by rw [h2]
    exact h3.symm
  have : Finite ↥S := Subgroup.instFiniteSubtypeMem S
  have : Group.IsNilpotent ↥S := hS.2.1.isNilpotent
  have hnil : Group.IsNilpotent ↥T := Subgroup.isNilpotent_of_ker_le_center ψ hker
  let P : Sylow 2 ↥T := default
  have htfae := Group.isNilpotent_of_finite_tfae (G := ↥T)
  have h14 := htfae.out 1 4
  have hPn : (P : Subgroup ↥T).Normal := h14.mp hnil 2 inferInstance P
  set U : Subgroup Q := (P : Subgroup ↥T).map T.subtype with hU
  refine ⟨U, ?_, Subgroup.map_subtype_le _, fun d hd => ?_⟩
  · refine K1.isSylowTwoOf_top_iff.mpr ⟨P.isPGroup'.map _, ?_⟩
    rw [hU, Subgroup.index_map_subtype]
    exact fun h => (Nat.prime_two.dvd_mul.mp h).elim P.not_dvd_index (index_comap_conj_odd hA hS)
  · have hdT := map_comap_conj hd
    have hle : U.map d.toMonoidHom ≤ T := by
      rw [← hT] at hdT
      rw [← hdT]
      exact Subgroup.map_mono (Subgroup.map_subtype_le _)
    have hV : IsPGroup 2 ↥((U.map d.toMonoidHom).subgroupOf T) :=
      ((P.isPGroup'.map T.subtype).map d.toMonoidHom).of_equiv
        (Subgroup.subgroupOfEquivOfLe hle).symm
    obtain ⟨P', hP'⟩ := hV.exists_le_sylow
    have hu : Unique (Sylow 2 ↥T) := Sylow.unique_of_normal P hPn
    have hPP : P' = P := Subsingleton.elim _ _
    have hle2 : U.map d.toMonoidHom ≤ U := by
      intro x hx
      have hx' : (⟨x, hle hx⟩ : ↥T) ∈ (P : Subgroup ↥T) := hPP ▸ hP' (show _ ∈ _ from hx)
      exact ⟨⟨x, hle hx⟩, hx', rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle2
      (by rw [Subgroup.card_map_of_injective (f := d.toMonoidHom) d.injective])

theorem le_of_le_normalizer_of_odd_index {X : Type*} [Group X] [Finite X] {T B : Subgroup X}
    (hT : IsPGroup 2 T) (hTB : T ≤ Subgroup.normalizer (B : Set X)) (hB : ¬ 2 ∣ B.index) :
    T ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : B.relIndex (T ⊔ B) = B.relIndex T := A4.relIndex_sup_eq_of_le_normalizer' hTB
  have h2 : B.relIndex T ∣ Nat.card T := Subgroup.relIndex_dvd_card B T
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have h3 : B.relIndex (T ⊔ B) ∣ B.index := Subgroup.relIndex_dvd_index_of_le le_sup_right
  rw [h1] at h3
  rw [hk] at h2
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have hi0 : i = 0 := by
    by_contra h
    apply hB
    rw [hi] at h3
    exact (dvd_pow_self 2 h).trans h3
  rw [hi0, pow_zero] at hi
  exact Subgroup.relIndex_eq_one.mp hi

theorem isSylowTwoOf_map_equiv {X Γ : Type} [Group X] [Group Γ] [Finite X] (e : X ≃* Γ)
    {T : Subgroup X} (hT : IsSylowTwoOf T ⊤) : IsSylowTwoOf (T.map e.toMonoidHom) ⊤ := by
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
  have : Finite Γ := Finite.of_equiv X e.toEquiv
  refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map _, ?_⟩
  rwa [show T.map e.toMonoidHom = T.map (e : X →* Γ) from rfl, Subgroup.index_map_equiv]

theorem eq_of_overgroups {X Γ : Type} [Group X] [Group Γ] [Finite X] [Finite Γ] (e : X ≃* Γ)
    {S₀ Y₀ : Subgroup Γ} (hS₀ : IsSylowTwoOf S₀ ⊤) {n : ℕ}
    (huniq : ∀ Z : Subgroup Γ, S₀ ≤ Z → Nat.card Z = n → Z = Y₀)
    {T Z₁ Z₂ : Subgroup X} (hT : IsSylowTwoOf T ⊤) (h1 : T ≤ Z₁) (h2 : T ≤ Z₂)
    (c1 : Nat.card Z₁ = n) (c2 : Nat.card Z₂ = n) : Z₁ = Z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' := isSylowTwoOf_map_equiv e hT
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS₀
  obtain ⟨hp', hi'⟩ := K1.isSylowTwoOf_top_iff.mp hT'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hp₀.toSylow hi₀) (hp'.toSylow hi')
  have hc : MulAut.conj g • S₀ = T.map e.toMonoidHom := by
    have := congrArg (fun P : Sylow 2 Γ => (P : Subgroup Γ)) hg
    simpa [Sylow.coe_subgroup_smul] using this
  have key : ∀ Z : Subgroup X, T ≤ Z → Nat.card Z = n →
      Z.map e.toMonoidHom = MulAut.conj g • Y₀ := by
    intro Z hTZ hZ
    have hle : S₀ ≤ (MulAut.conj g)⁻¹ • Z.map e.toMonoidHom :=
      Subgroup.pointwise_smul_subset_iff.mp (hc ▸ Subgroup.map_mono hTZ)
    have hcard : Nat.card ↥((MulAut.conj g)⁻¹ • Z.map e.toMonoidHom) = n := by
      rw [← Nat.card_congr (Subgroup.equivSMul _ _).toEquiv,
        Subgroup.card_map_of_injective e.injective, hZ]
    rw [← huniq _ hle hcard, smul_inv_smul]
  exact Subgroup.map_injective e.injective ((key Z₁ h1 c1).trans (key Z₂ h2 c2).symm)

theorem card_of_isExt {X : Type} [Group X] {PV PY : ∀ (V : Type) [Group V], Prop} {a b : ℕ}
    (hV : ∀ (V : Type) [Group V], PV V → Nat.card V = a)
    (hY : ∀ (Y : Type) [Group Y], PY Y → Nat.card Y = b) (h : IsExt X PV PY) :
    Nat.card X = a * b := by
  obtain ⟨V, _, hPV, hPY⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup V, hY _ hPY, hV _ hPV, mul_comm]

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hZ | hZ
  · exact hZ
  · exfalso
    have hnorm : ∀ x : G, (Subgroup.zpowers x).Normal := fun x => by
      refine ⟨fun a ha y => ?_⟩
      have hy : y ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top y
      rwa [(Subgroup.mem_center_iff.mp hy a).symm, mul_inv_cancel_right]
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    have hg' : Subgroup.zpowers g = ⊤ := by
      have := hnorm g
      exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g)).resolve_left
        fun h1 => hg (Subgroup.zpowers_eq_bot.mp h1)
    have hcard : Nat.card G = orderOf g := by
      rw [← Nat.card_zpowers, hg', Subgroup.card_top]
    have hne1 : orderOf g ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]
      exact hg
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
    have hord : orderOf (g ^ (orderOf g / p)) = p :=
      orderOf_pow_orderOf_div (orderOf_pos g).ne' hpd
    have := hnorm (g ^ (orderOf g / p))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (g ^ (orderOf g / p)))
      with h1 | h1
    · rw [Subgroup.zpowers_eq_bot.mp h1, orderOf_one] at hord
      exact hp.one_lt.ne' hord.symm
    · have h2 := Nat.card_zpowers (g ^ (orderOf g / p))
      rw [h1, Subgroup.card_top, hord] at h2
      exact h (by rw [h2]; exact hp)

end CFSG.Quasithin.H13.KG3312
