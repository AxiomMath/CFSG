module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838A
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem838B
public import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.E1.LiftS5
open scoped IsMulCommutative

namespace Ch838

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_he {Q : Type} [Group Q]
    (e : Q ≃* NativeSporadic.Carrier .He) : Subgroup.center Q = ⊥ := by
  have : IsSimpleGroup (NativeSporadic.Carrier .He) := CFSG.Sporadic.He.isSimpleGroup_He
  have hs : IsSimpleGroup Q := MulEquiv.isSimpleGroup e
  have hcard : Nat.card Q = 4030387200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.He.card_He
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : Q, a * b = b * a := fun a b => by
      have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hc }
    have hp := IsSimpleGroup.prime_card (α := Q)
    rw [hcard] at hp
    exact absurd hp (by norm_num)

omit [Finite G] in
theorem commutator_mem_of_quotConj_eq_one {K : Subgroup G}
    {g : ↥(Subgroup.normalizer (K : Set G))} (h : quotConj K g = 1) :
    ∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  intro k hk
  have h1 := congrArg (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) =>
    φ ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)) h
  change ((K.normalizerMonoidHom g ⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) =
    ((⟨k, hk⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) at h1
  rw [QuotientGroup.eq] at h1
  have hval : ((K.normalizerMonoidHom g ⟨k, hk⟩ : ↥K) : G) = (g : G) * k * (g : G)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe K g ⟨k, hk⟩
  set a := K.normalizerMonoidHom g ⟨k, hk⟩ with ha
  have h2 : a * (⟨k, hk⟩ : ↥K)⁻¹ ∈ CFSG.pCore 2 ↥K := by
    have h3 := (CFSG.pCore_normal (p := 2) (G := ↥K)).conj_mem _ (inv_mem h1) a
    simpa [mul_assoc] using h3
  have h4 : ((a * (⟨k, hk⟩ : ↥K)⁻¹ : ↥K) : G) ∈ pCoreOf 2 K := by
    rw [CFSG.Open.pCoreOf]
    exact ⟨_, h2, rfl⟩
  simpa [hval] using h4

theorem exists_isHStar_twoResidual_le {T M U : Subgroup G} (hT2 : IsPGroup 2 T) (hUT : U ≤ T)
    (hU1 : U ≠ ⊥) (hTU : T ≤ Subgroup.normalizer (U : Set G))
    (hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    ∃ H : Subgroup G, IsHStar T M H ∧ twoResidual H ≤ Subgroup.centralizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (U : Set G) with hC
  set K := C ⊔ T with hK
  have hKN : K ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer _) hTU
  have hUO : U ≤ pCoreOf 2 K :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hUT.trans le_sup_right) hKN
      (hT2.to_le hUT)
  have hKH : InH T K := ⟨le_sup_right, fun h => hU1 (le_bot_iff.mp (h ▸ hUO))⟩
  have hKM : ¬ K ≤ M := fun h => hCM (le_sup_left.trans h)
  obtain ⟨H, -, hHmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun Y : Subgroup G => InH T Y ∧ ¬ Y ≤ M ∧ Y ≤ K) K ⟨hKH, hKM, le_rfl⟩
  have hHK : H ≤ K := hHmin.1.2.2
  refine ⟨H, ⟨hHmin.1.1, hHmin.1.2.1, fun Y hY hYH hYM => le_antisymm hYH
    (hHmin.2 ⟨hY, hYM, hYH.trans hHK⟩ hYH)⟩, ?_⟩
  have hKC : K ≤ Subgroup.normalizer (C : Set G) :=
    sup_le Subgroup.le_normalizer (hTU.trans (normalizer_le_normalizer_centralizer U))
  have h2 := B6.isTwoQuotient_of_sup_eq hT2 hKC (sup_comm T C)
  refine (twoResidual_le_of_isTwoQuotient (N := C ⊓ H) inf_le_right ?_ ?_).trans inf_le_left
  · intro h hh
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hKC (hHK hh), Subgroup.le_normalizer hh⟩
  · intro y hy
    obtain ⟨k, hk⟩ := h2 y (hHK hy)
    exact ⟨k, hk, H.pow_mem hy _⟩

theorem le_normalizer_of_cComp_pair {Y K₁ K₂ I : Subgroup G} (h₁ : K₁ ∈ cComp Y)
    (h₂ : K₂ ∈ cComp Y) (hne : K₁ ≠ K₂)
    (hYN : Y ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G)) (hIY : I ≤ Y)
    (hI : twoResidual I = I) :
    I ≤ Subgroup.normalizer (K₁ : Set G) ⊓ Subgroup.normalizer (K₂ : Set G) := by
  have hperm : ∀ g ∈ Y, ∀ {K}, K ∈ cComp Y → K ≤ K₁ ⊔ K₂ →
      conjSub g K = K₁ ∨ conjSub g K = K₂ := by
    intro g hg K hK hKle
    refine SBc13.eq_or_eq_of_mem_cComp_of_le_sup h₁ h₂ (conjSub_mem_cComp_of_mem hK hg) ?_
    calc conjSub g K ≤ conjSub g (K₁ ⊔ K₂) := CFSG.Quasithin.conjSub_mono g hKle
      _ = K₁ ⊔ K₂ := F7.conjSub_eq_of_mem_normalizer (hYN hg)
  have hp₁ := fun g (hg : g ∈ Y) => hperm g hg h₁ le_sup_left
  have hp₂ := fun g (hg : g ∈ Y) => hperm g hg h₂ le_sup_right
  set N := Subgroup.normalizer (K₁ : Set G) ⊓ Subgroup.normalizer (K₂ : Set G) with hN
  have hfix : ∀ x ∈ N, conjSub x K₁ = K₁ ∧ conjSub x K₂ = K₂ := fun x hx =>
    ⟨F7.conjSub_eq_of_mem_normalizer hx.1, F7.conjSub_eq_of_mem_normalizer hx.2⟩
  have hmemN : ∀ x : G, conjSub x K₁ = K₁ → conjSub x K₂ = K₂ → x ∈ N := fun x h1 h2 =>
    ⟨CosetGeom.mem_normalizer_of_conjSub_eq h1, CosetGeom.mem_normalizer_of_conjSub_eq h2⟩
  have hYNN : Y ≤ Subgroup.normalizer (N : Set G) := by
    have key : ∀ h ∈ Y, ∀ x ∈ N, h * x * h⁻¹ ∈ N := by
      intro h hh x hx
      have hK : ∀ {K}, (conjSub h⁻¹ K = K₁ ∨ conjSub h⁻¹ K = K₂) →
          conjSub (h * x * h⁻¹) K = K := by
        intro K hK
        rw [SBc13.conjSub_mul', SBc13.conjSub_mul']
        have h3 : conjSub x (conjSub h⁻¹ K) = conjSub h⁻¹ K := by
          rcases hK with h4 | h4 <;> rw [h4]
          · exact (hfix x hx).1
          · exact (hfix x hx).2
        rw [h3, ← SBc13.conjSub_mul', mul_inv_cancel]
        ext y
        simp [mem_conjSub]
      exact hmemN _ (hK (hp₁ _ (Y.inv_mem hh))) (hK (hp₂ _ (Y.inv_mem hh)))
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key h hh x, fun hx => ?_⟩
    have := key h⁻¹ (Y.inv_mem hh) _ hx
    simpa [mul_assoc] using this
  refine le_of_pow_mem_of_twoResidual_eq hI (hIY.trans hYNN) fun g hg => ?_
  have hgY := hIY hg
  have hinj : ∀ {A B : Subgroup G}, conjSub g A = conjSub g B → A = B :=
    fun h => (conjSub_inj g).mp h
  rcases hp₁ g hgY with h1 | h1
  ·
    have h2 : conjSub g K₂ = K₂ := by
      rcases hp₂ g hgY with h2 | h2
      · exact absurd (hinj (h2.trans h1.symm)) (Ne.symm hne)
      · exact h2
    exact ⟨0, by rw [pow_zero, pow_one]; exact hmemN g h1 h2⟩
  ·
    have h2 : conjSub g K₂ = K₁ := by
      rcases hp₂ g hgY with h2 | h2
      · exact h2
      · exact absurd (hinj (h2.trans h1.symm)) (Ne.symm hne)
    refine ⟨1, hmemN _ ?_ ?_⟩
    · rw [pow_one, pow_two, SBc13.conjSub_mul', h1, h2]
    · rw [pow_one, pow_two, SBc13.conjSub_mul', h2, h1]

omit [Finite G] in
theorem commutator_mem_of_sup {D₁ D₂ N : Subgroup G} {t : G}
    (hN : D₁ ⊔ D₂ ≤ Subgroup.normalizer (N : Set G))
    (h₁ : ∀ d ∈ D₁, t * d * t⁻¹ * d⁻¹ ∈ N) (h₂ : ∀ d ∈ D₂, t * d * t⁻¹ * d⁻¹ ∈ N) :
    ∀ d ∈ D₁ ⊔ D₂, t * d * t⁻¹ * d⁻¹ ∈ N := by
  let D' : Subgroup G :=
    { carrier := {d | d ∈ Subgroup.normalizer (N : Set G) ∧ t * d * t⁻¹ * d⁻¹ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, ?_⟩
        have e : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
            (t * a * t⁻¹ * a⁻¹) * (a * (t * b * t⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact N.mul_mem ha' ((Subgroup.mem_normalizer_iff.mp ha _).mp hb')
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, ?_⟩
        have e : t * a⁻¹ * t⁻¹ * a⁻¹⁻¹ = a⁻¹ * (t * a * t⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) _).mp (N.inv_mem ha') }
  have hle : D₁ ⊔ D₂ ≤ D' := sup_le (fun d hd => ⟨hN (Subgroup.mem_sup_left hd), h₁ d hd⟩)
    (fun d hd => ⟨hN (Subgroup.mem_sup_right hd), h₂ d hd⟩)
  exact fun d hd => (hle hd).2

theorem inf_le_pCoreOf_of_cases
    (hOut : KG838Out) (hPar : KG838Par) {Gz Kz T I : Subgroup G} (hTGz : T ≤ Gz)
    (hT2 : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index) (hKzGz : Kz ≤ Gz)
    (hKzN : Gz ≤ Subgroup.normalizer (Kz : Set G)) (hIGz : I ≤ Gz) (hI : twoResidual I = I)
    (hI3 : ¬ 3 ∣ Nat.card I) (hTI : T ≤ Subgroup.normalizer (I : Set G))
    (hcases : (∃ (K : Subgroup G) (s : G), s ∈ T ∧ s ∉ Subgroup.normalizer (K : Set G) ∧
        quasithinIsCComponent K Gz ∧ Kz = K ⊔ CFSG.conjugate K s ∧ ∃ p : ℕ, p.Prime ∧
          CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 2 p 1) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Kz ⧸ CFSG.pCore 2 ↥Kz) .PSL 4 2 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Kz ⧸ CFSG.pCore 2 ↥Kz) .PSL 5 2 1 ∨
      Nonempty (↥Kz ⧸ CFSG.pCore 2 ↥Kz ≃* NativeSporadic.Carrier .He)) :
    T ⊓ I ≤ pCoreOf 2 (Kz ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTKz : T ≤ Subgroup.normalizer (Kz : Set G) := hTGz.trans hKzN
  have hTW : T ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTI ht⟩
  have h2elt : ∀ t ∈ T, ∃ n : ℕ, t ^ 2 ^ n = 1 := fun t ht => by
    obtain ⟨n, hn⟩ := hT2 ⟨t, ht⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  refine le_pCoreOf_sup_of_commutator_mem hT2 hTKz inf_le_left hTW ?_
  rcases hcases with ⟨K, s, hsT, hsN, hKC, hKz, p, -, hmod⟩ | hcase
  ·
    subst hKz
    have hK : K ∈ cComp Gz := hKC
    have hsGz : s ∈ Gz := hTGz hsT
    have hK₂ : CFSG.conjugate K s ∈ cComp Gz := conjSub_mem_cComp_of_mem hK (Gz.inv_mem hsGz)
    have hne : K ≠ CFSG.conjugate K s := fun h =>
      hsN (Vol2.Ch10.SecA.conjugate_eq_self_iff.mp h.symm)
    have hIKK := le_normalizer_of_cComp_pair hK hK₂ hne hKzN hIGz hI
    have hIK : I ≤ Subgroup.normalizer (K : Set G) := fun x hx => (hIKK hx).1
    have hOut1 : OutIsTwoGroup (↥K ⧸ CFSG.pCore 2 ↥K) := hOut.1 _ p hmod
    have hcen1 := F420.center_eq_bot_of_statedPSL hmod
    have hY3 : ¬ 3 ∣ Nat.card (projQ K I) := fun h =>
      hI3 (h.trans (card_projQ_dvd hOut1 hcen1 hIK hI))
    have hnil := twoNilpotent_of_psl2 hmod (projQ K I) hY3
    have hCK : ∀ t ∈ T ⊓ I, ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro t ht k hk
      obtain ⟨n, hn⟩ := h2elt t ht.1
      exact commutator_mem_of_quotConj_eq_one
        (quotConj_eq_one_of_twoNilpotent hOut1 hcen1 hIK hI hnil ⟨t, hIK ht.2⟩ ht.2 hn) k hk
    have hCK₂ : ∀ t ∈ T ⊓ I, ∀ k ∈ CFSG.conjugate K s,
        t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 (CFSG.conjugate K s) := by
      intro t ht k hk
      have ht' : s * t * s⁻¹ ∈ T ⊓ I := (Subgroup.mem_normalizer_iff.mp (hTW hsT) t).mp ht
      have hk' : s * k * s⁻¹ ∈ K := Vol2.Ch10.SecA.mem_conjugate_iff.mp hk
      have h1 := hCK _ ht' _ hk'
      rw [Vol2.Ch10.SecA.pCoreOf_conjugate, Vol2.Ch10.SecA.mem_conjugate_iff]
      have e : s * (t * k * t⁻¹ * k⁻¹) * s⁻¹ =
          s * t * s⁻¹ * (s * k * s⁻¹) * (s * t * s⁻¹)⁻¹ * (s * k * s⁻¹)⁻¹ := by group
      rw [e]
      exact h1
    have hO₁ : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ CFSG.conjugate K s) := by
      rw [← Vol2.Ch10.SecA.inf_pCoreOf_eq_of_normal le_sup_left
        (SBc16.sup_le_normalizer_of_mem_cComp hK hK₂)]
      exact inf_le_right
    have hO₂ : pCoreOf 2 (CFSG.conjugate K s) ≤ pCoreOf 2 (K ⊔ CFSG.conjugate K s) := by
      rw [← Vol2.Ch10.SecA.inf_pCoreOf_eq_of_normal le_sup_right
        (sup_comm K (CFSG.conjugate K s) ▸ SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK)]
      exact inf_le_right
    intro t ht d hd
    exact commutator_mem_of_sup (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (fun k hk => hO₁ (hCK t ht k hk)) (fun k hk => hO₂ (hCK₂ t ht k hk)) d hd
  ·
    have hIK : I ≤ Subgroup.normalizer (Kz : Set G) := hIGz.trans hKzN
    have hOutKz : OutIsTwoGroup (↥Kz ⧸ CFSG.pCore 2 ↥Kz) := by
      rcases hcase with h | h | h
      · exact hOut.2.1 _ h
      · exact hOut.2.2.1 _ h
      · exact hOut.2.2.2 _ h
    have hcen : Subgroup.center (↥Kz ⧸ CFSG.pCore 2 ↥Kz) = ⊥ := by
      rcases hcase with h | h | h
      · exact F420.center_eq_bot_of_statedPSL h
      · exact F420.center_eq_bot_of_statedPSL h
      · obtain ⟨e⟩ := h
        exact center_eq_bot_of_he e
    have hTsyl : IsSylowIn 2 T (Kz ⊔ T) :=
      ⟨le_sup_right, hT2, fun h => hTidx (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    have hSK : IsSylowIn 2 (T ⊓ Kz) Kz :=
      B6.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le Subgroup.le_normalizer hTKz)
    set Sb : Sylow 2 (↥Kz ⧸ CFSG.pCore 2 ↥Kz) :=
      hSK.toSylow.mapSurjective (QuotientGroup.mk'_surjective _) with hSbdef
    have hSbN : (Sb : Subgroup _) ≤
        Subgroup.normalizer ((projQ Kz I : Subgroup _) : Set (↥Kz ⧸ CFSG.pCore 2 ↥Kz)) := by
      rw [hSbdef, Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
      exact le_normalizer_projQ inf_le_right fun t ht => hTI ht.1
    have hY3 : ¬ 3 ∣ Nat.card (projQ Kz I) := fun h =>
      hI3 (h.trans (card_projQ_dvd hOutKz hcen hIK hI))
    have hle : projQ Kz I ≤ Sb := hPar _ hcase Sb _ hSbN hY3
    have hnil : TwoNilpotent ↥(projQ Kz I) := twoNilpotent_of_isPGroup (Sb.isPGroup'.to_le hle)
    intro t ht d hd
    obtain ⟨n, hn⟩ := h2elt t ht.1
    exact commutator_mem_of_quotConj_eq_one
      (quotConj_eq_one_of_twoNilpotent hOutKz hcen hIK hI hnil ⟨t, hIK ht.2⟩ ht.2 hn) d hd

omit [Finite G] in
theorem pCoreOf_le_ch83S [Finite G] {T L : Subgroup G} {z : G} (hT2 : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) : pCoreOf 2 (ch83Kz T L z ⊔ T) ≤ ch83S T L z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hTsyl : IsSylowIn 2 T (ch83Kz T L z ⊔ T) :=
    ⟨le_sup_right, hT2, fun h => hTidx (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le_of_isSylowIn hTsyl).trans le_sup_right)
    ((sup_le_sup_right hXKz T).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem false_of_inf_le_ch83S (h836 : Stmt8_3_6) {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Row711L3Wreath T L I)
    {z : G} (hz2 : orderOf z = 2)
    (hzV : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hIS : T ⊓ twoResidual H ≤ ch83S T L z)
    (hzS : z ∈ ch83S T L z) (hsolv : Group.IsSolvable ↥(twoResidual H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ir := twoResidual H with hIr
  set S := ch83S T L z with hSdef
  have hTsyl : ∀ K : Subgroup G, T ≤ K → IsSylowIn 2 T K := fun K hTK =>
    ⟨hTK, hyp.fsu.sylow.1, fun h2 => hyp.fsu.sylow.2
      (h2.trans (Subgroup.relIndex_dvd_index_of_le hTK))⟩
  have hST : S ≤ T := pCoreOf_le_of_isSylowIn (hTsyl _ le_sup_right)
  have hTH : T ≤ H := hH.1.1
  have hHIr : H ≤ Subgroup.normalizer (Ir : Set G) := le_normalizer_twoResidual H
  have hSIr : S ≤ Subgroup.normalizer (Ir : Set G) := hST.trans (hTH.trans hHIr)
  have hTI : IsSylowIn 2 (T ⊓ Ir) Ir :=
    B6.isSylowTwoOf_inf_normal (hTsyl H hTH) (twoResidual_le H) hHIr
  have hSyl : IsSylowIn 2 S (Ir ⊔ S) := by
    refine ⟨le_sup_right, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _, ?_⟩
    rw [sup_comm,
      CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses.relIndex_sup_eq_relIndex hSIr,
      ← Subgroup.inf_relIndex_right]
    have heq : S ⊓ Ir = T ⊓ Ir :=
      le_antisymm (inf_le_inf_right _ hST) (le_inf hIS inf_le_right)
    rw [heq]
    exact hTI.not_dvd_relIndex
  have hIrN : Ir ⊔ S ≤ Subgroup.normalizer (Ir : Set G) := sup_le Subgroup.le_normalizer hSIr
  have hnorm : (Ir.subgroupOf (Ir ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hIrN
  have h2q := B6.isTwoQuotient_of_sup_eq (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hIrN
    (sup_comm S Ir)
  have hq2 : IsPGroup 2 (↥(Ir ⊔ S) ⧸ Ir.subgroupOf (Ir ⊔ S)) := by
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := h2q y hy
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have : Group.IsSolvable ↥Ir := hsolv
  have : Group.IsSolvable (↥(Ir ⊔ S) ⧸ Ir.subgroupOf (Ir ⊔ S)) := by
    have := hq2.isNilpotent
    infer_instance
  have hsolvIS : Group.IsSolvable ↥(Ir ⊔ S) :=
    Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_sup_left : Ir ≤ Ir ⊔ S))
      (QuotientGroup.mk' (Ir.subgroupOf (Ir ⊔ S))) (by
        rintro x hx
        rw [QuotientGroup.ker_mk'] at hx
        exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩)
  have hn1 : E1.nParam (Ir ⊔ S) = 1 := by
    have hle1 := E1.solvable_nParam_le_one hsolvIS
    have hne0 : ¬ E1.nParam (Ir ⊔ S) ≤ 0 := fun h => by
      have hodd := E1.odd_of_nParam_le_zero h
      have h2 : 2 ∣ Nat.card ↥(Ir ⊔ S) := by
        rw [← hz2]
        exact Subgroup.orderOf_dvd_natCard _ ((le_sup_right : S ≤ _) hzS)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hle1)
    rw [← hk] at hle1 hne0 ⊢
    have hk1 : k ≤ 1 := by exact_mod_cast hle1
    have hk0 : k ≠ 0 := fun h => hne0 (by rw [h]; simp)
    have hk' : k = 1 := by omega
    rw [hk']
    rfl
  have hle := h836 G T L I hyp h731 hc hrow z hz2 hzV (Ir ⊔ S) hSyl hn1
  apply hH.2.1
  rw [← sup_twoResidual_eq (hTsyl H hTH)]
  exact sup_le (le_normalizer_conjClosure L T) (le_sup_left.trans hle)

end Ch838

@[expose] def Claim838Solv : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    ∀ _ : IsMulCommutative ↥(fsuV T I), Row711L3Wreath T L I →
    ∀ (hV : IsElemAbelian 2 (fsuV T I)) (H : Subgroup G), IsHStar T (fsuM T L) H →
      twoResidual H ≤ Subgroup.centralizer (ch83CR hV : Set G) →
        Group.IsSolvable ↥(twoResidual H)

theorem stmt8_3_8_of
    (h37 : CFSG.QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) (hmod : StmtFSUModule)
    (h326 : Stmt3_2_6C) (h836 : Stmt8_3_6) (h837 : Stmt8_3_7) (hOut : KG838Out)
    (hPar : KG838Par) (hsolv : Claim838Solv) : Stmt8_3_8 := by
  intro G _ _ T L I hyp h731 hc hrow hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  by_contra hCM
  obtain ⟨z, hz2, hzV⟩ := input8_3_z G T L I hyp h731 hc hrow
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hzT : z ∈ T := fsuV_le_T hyp.fsu hV hN hzmem.1
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hzU : z ∈ ch83CR hV := Ch838.mem_ch83CR hV hzmem
  have hU1 : ch83CR hV ≠ ⊥ := fun h => hz1 (by
    have := hzU
    rwa [h, Subgroup.mem_bot] at this)
  have hUT : ch83CR hV ≤ T := by
    rintro _ ⟨v, -, rfl⟩
    exact fsuV_le_T hyp.fsu hV hN v.val_mem
  have hTU := Ch838.le_normalizer_ch83CR hV hTV
  obtain ⟨H, hH, hIU⟩ := Ch838.exists_isHStar_twoResidual_le hyp.fsu.sylow.1 hUT hU1 hTU hCM
  have hCz : Subgroup.centralizer (ch83CR hV : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hzU)
  have hIGz : twoResidual H ≤ Subgroup.centralizer ({z} : Set G) := hIU.trans hCz
  have h3 := Ch838.not_three_dvd_card_centralizer_ch83CR h37 h38 h326 hyp hV hrow hN hU1
  have hI3 : ¬ 3 ∣ Nat.card ↥(twoResidual H) := fun h =>
    h3 (h.trans (Subgroup.card_dvd_of_le hIU))
  have hTI : T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    hH.1.1.trans (le_normalizer_twoResidual H)
  obtain ⟨-, hcases⟩ := h837 G T L I hyp h731 hc hrow z hz2 hzV
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hGzKz : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (ch83Kz T L z : Set G) := le_normalizer_conjClosure _ _
  have hIO := Ch838.inf_le_pCoreOf_of_cases hOut hPar hTz hyp.fsu.sylow.1 hyp.fsu.sylow.2
    hKzGz hGzKz hIGz (twoResidual_twoResidual H) hI3 hTI hcases
  have hOS := Ch838.pCoreOf_le_ch83S (L := L) (z := z) hyp.fsu.sylow.1 hyp.fsu.sylow.2
  have hzS : z ∈ ch83S T L z := by
    have hzn : Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
      Ch8310.le_normalizer_of_comm fun a ha b hb => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have hb' : Commute z b := Subgroup.mem_centralizer_iff.1 hb z rfl
        exact (hb'.zpow_left k).eq
    have hz2grp : IsPGroup 2 (Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one])
    have h1 : Subgroup.zpowers z ≤ ch83S T L z :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.zpowers_le).mpr ((le_sup_right : T ≤ ch83X T L z ⊔ T) hzT))
        ((sup_le hXGz hTz).trans hzn) hz2grp
    exact h1 (Subgroup.mem_zpowers z)
  exact Ch838.false_of_inf_le_ch83S h836 hyp h731 hrow hz2 hzV hH (hIO.trans hOS) hzS
    (hsolv G T L I hyp h731 hc hrow hV H hH hIU)

end CFSG.Quasithin.H13
