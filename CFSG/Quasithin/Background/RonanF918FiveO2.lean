module

public import CFSG.Quasithin.Vol2.Ch3T326PM
public import CFSG.Quasithin.Background.RonanF918Five

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement Matrix

section Groups

theorem oTwoUpper_eq_oTwoRes {X : Type} [Group X] (A : Subgroup X) : oTwoUpper A = oTwoRes A := by
  unfold oTwoUpper oTwoRes
  congr 1
  ext x
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, orderOf x, ho, pow_orderOf_eq_one x⟩
  · rintro ⟨hx, m, hm, hxm⟩
    refine ⟨hx, ?_⟩
    obtain ⟨k, hk⟩ := orderOf_dvd_of_pow_eq_one hxm
    exact (Nat.odd_mul.mp (hk ▸ hm)).1

theorem nonempty_mulEquiv_zmod_five {P : Type} [Group P] (hP : Nat.card P = 5) :
    Nonempty (P ≃* Multiplicative (ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : IsCyclic P := isCyclic_of_prime_card hP
  exact ⟨(zmodCyclicMulEquiv (inferInstance : IsCyclic P)).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hP).toAddEquiv)⟩

theorem nonempty_mulEquiv_zmod_five_prod {P : Type} [Group P] (hP : Nat.card P = 25)
    (hexp : ∀ x : P, x ^ 5 = 1) :
    Nonempty (P ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hP' : Nat.card P = 5 ^ 2 := by rw [hP]; norm_num
  letI : CommGroup P := IsPGroup.commGroupOfCardEqPrimeSq hP'
  have h5 : ∀ x : Additive P, (5 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    simpa using hexp (Additive.toMul x)
  letI : Module (ZMod 5) (Additive P) := AddCommGroup.zmodModule h5
  haveI : Finite (Additive P) := Finite.of_equiv P Additive.ofMul
  letI : Fintype (Additive P) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod 5) (Additive P) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod 5) (Additive P) = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 5) (V := Additive P)
    have h2 : Fintype.card (Additive P) = 5 ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact (Nat.card_congr Additive.toMul).trans hP'
    rw [h2, ZMod.card] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 5) h1).symm
  let b := Module.finBasisOfFinrankEq (ZMod 5) (Additive P) hfr
  let e1 : Additive P ≃+ ZMod 5 × ZMod 5 :=
    (b.equivFun.toAddEquiv).trans (LinearEquiv.finTwoArrow (ZMod 5) (ZMod 5)).toAddEquiv
  let e2 : P ≃* Multiplicative (ZMod 5 × ZMod 5) := AddEquiv.toMultiplicative e1
  exact ⟨e2.trans (MulEquiv.prodMultiplicative (ZMod 5) (ZMod 5))⟩

theorem nonempty_mulEquiv_five_of_card {X : Type} [Group X] {A : Subgroup X}
    (h : Nat.card ↥(oTwoUpper A) = 5 ∨
      (Nat.card ↥(oTwoUpper A) = 25 ∧ ∀ x ∈ oTwoUpper A, x ^ 5 = 1)) :
    Nonempty (↥(oTwoRes A) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(oTwoRes A) ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) := by
  rw [← oTwoUpper_eq_oTwoRes]
  rcases h with h5 | ⟨h25, hexp⟩
  · exact Or.inl (nonempty_mulEquiv_zmod_five h5)
  · exact Or.inr (nonempty_mulEquiv_zmod_five_prod h25 (fun x => Subtype.ext (hexp x.1 x.2)))

end Groups

section Kernel

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup {P A B : Subgroup G} (hA : A ≤ Subgroup.normalizer (P : Set G))
    (hB : B ≤ Subgroup.normalizer (P : Set G)) (hcomm : ⁅A, B⁆ ≤ P) :
    ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, ∃ p ∈ P, x = a * b * p := by
  set S : Set G := {y | ∃ a ∈ A, ∃ b ∈ B, ∃ p ∈ P, y = a * b * p} with hS
  have hc : ∀ g ∈ A ⊔ B, ∀ p ∈ P, g * p * g⁻¹ ∈ P := fun g hg p hp =>
    (Subgroup.mem_normalizer_iff.mp (sup_le hA hB hg) p).mp hp
  have hc' : ∀ g ∈ A ⊔ B, ∀ p ∈ P, g⁻¹ * p * g ∈ P := fun g hg p hp => by
    simpa using hc g⁻¹ ((A ⊔ B).inv_mem hg) p hp
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    rintro _ ⟨a, ha, b, hb, p, hp, rfl⟩ _ ⟨a', ha', b', hb', p', hp', rfl⟩
    have hc1 : b⁻¹ * a'⁻¹ * b * a' ∈ P := by
      have h1 : ⁅b⁻¹, a'⁻¹⁆ ∈ ⁅B, A⁆ :=
        Subgroup.commutator_mem_commutator (B.inv_mem hb) (A.inv_mem ha')
      rw [Subgroup.commutator_comm] at h1
      have e : ⁅b⁻¹, a'⁻¹⁆ = b⁻¹ * a'⁻¹ * b * a' := by
        simp [commutatorElement_def]
      exact e ▸ hcomm h1
    have hAB : ∀ g ∈ A, g ∈ A ⊔ B := fun g hg => Subgroup.mem_sup_left hg
    have hBA : ∀ g ∈ B, g ∈ A ⊔ B := fun g hg => Subgroup.mem_sup_right hg
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb',
      (b'⁻¹ * (b⁻¹ * a'⁻¹ * b * a') * b') * (b'⁻¹ * (a'⁻¹ * p * a') * b') * p',
      P.mul_mem (P.mul_mem ?_ ?_) hp', ?_⟩
    · simpa using hc' b' (hBA b' hb') _ hc1
    · have := hc' a' (hAB a' ha') p hp
      simpa using hc' b' (hBA b' hb') _ this
    · group
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => y ∈ S) ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, B.one_mem, 1, P.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, 1, P.one_mem, by simp⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, 1, P.one_mem, by simp⟩
  · intro y z _ _ hy hz
    exact hmul y hy z hz
  · rintro y _ ⟨a, ha, b, hb, p, hp, rfl⟩
    have h1 : (p⁻¹ : G) ∈ S := ⟨1, A.one_mem, 1, B.one_mem, p⁻¹, P.inv_mem hp, by simp⟩
    have h2 : (b⁻¹ : G) ∈ S := ⟨1, A.one_mem, b⁻¹, B.inv_mem hb, 1, P.one_mem, by simp⟩
    have h3 : (a⁻¹ : G) ∈ S := ⟨a⁻¹, A.inv_mem ha, 1, B.one_mem, 1, P.one_mem, by simp⟩
    have := hmul _ (hmul _ h1 _ h2) _ h3
    simpa [mul_assoc] using this

end Kernel

section Kernel2

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}
  [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem center_eq_bot_of_simple_perfect {X : Type} [Group X] [IsSimpleGroup X]
    (hp : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  rcases (inferInstance : (Subgroup.center X).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have h1 : commutator X = ⊥ := (commutator_eq_bot_iff_center_eq_top X).mpr h
    have h2 : commutator X = ⊤ := hp.commutator_eq_top
    rw [h1] at h2
    haveI : Nontrivial X := IsSimpleGroup.toNontrivial
    exact bot_ne_top h2

theorem ker_toAutI_le_pCore (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hne : autIH V₁ I H K ≠ ⊥) :
    (toAutI h I).ker ≤ CFSG.pCore 2 ↥K := by
  have hker : CFSG.pCore 2 ↥K ≤ (toAutI h I).ker := by
    rw [← F918Fine4Pf.ker_toAutI_eq_pCore h]
    exact toAutI_ker_le h hIU
  let f : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autIH V₁ I H K) :=
    QuotientGroup.lift _ (toAutI h I) hker
  have hinj : Function.Injective f := by
    apply injective_of_isSimpleGroup
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    obtain ⟨s, hs⟩ := toAutI_surjective h I y
    exact ⟨QuotientGroup.mk s, fun h1 => hy1 (by rw [← hs]; exact h1)⟩
  intro x hx
  have h1 : f (QuotientGroup.mk x) = 1 := hx
  have h2 := hinj (h1.trans (map_one f).symm)
  exact (QuotientGroup.eq_one_iff x).mp h2

theorem mem_pCoreOf_of_mem_K_of_actH_eq_one (h : HypF918 T V L V₁ Vp H K)
    (hIU : I ≤ conjClosure Vp H) (hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hne : autIH V₁ I H K ≠ ⊥) {x : G} (hxK : x ∈ K)
    (hx : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
      ⟨x, (le_of_mem_cComp h.K_cComp) hxK⟩ = 1) : x ∈ pCoreOf 2 H := by
  have h1 : (⟨x, hxK⟩ : ↥K) ∈ (toAutI h I).ker := by
    rw [MonoidHom.mem_ker, toAutI_eq_one_iff]
    exact hx
  have h2 := ker_toAutI_le_pCore h hIU hS hne h1
  rw [← F918Fine4Pf.ker_toAutI_eq_pCore h, MonoidHom.mem_ker, toAutI_eq_one_iff] at h2
  exact mem_pCoreOf_of_actH_eq_one h h2

theorem ker_K₀_le_pCore (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {n : G}
    (hnK : n ∈ conjClosure K T)
    (hact : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨n, h.K₀_le_H hnK⟩ = 1) :
    n ∈ pCoreOf 2 H := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  obtain ⟨t, ht, htK⟩ := exists_mem_T_not_normalizer h hK
  have htH : t ∈ H := h.T_le_H ht
  obtain ⟨hA38K, hdata⟩ := five_group_data h hH hA37 hA38 hK
  obtain ⟨hKt, hK₀, hcomm, -⟩ := hdata t ht htK
  have hS : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA38K
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  have hKtH : K.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hKt
  have hPH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hc : ∀ g ∈ H, ∀ p ∈ pCoreOf 2 H, g * p * g⁻¹ ∈ pCoreOf 2 H := fun g hg p hp =>
    (Subgroup.mem_normalizer_iff.mp (hPH hg) p).mp hp
  have hLsimple : IsSimpleGroup ↥(autIH V₁ I H K) := by
    have := (five_prelim h hH hK hIU hnt hA37 hA38).1
    exact CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types this
  have hperf := F918Fine4Pf.isPerfect_autIH h I
  have hcen : Subgroup.center ↥(autIH V₁ I H K) = ⊥ := center_eq_bot_of_simple_perfect hperf
  obtain ⟨a, ha, b, hb, p, hp, hn⟩ := exists_mul_of_mem_sup (hKH.trans hPH) (hKtH.trans hPH) hcomm n
    (hK₀ ▸ hnK)
  subst hn
  have haH : a ∈ H := hKH ha
  have hbH : b ∈ H := hKtH hb
  have hpH : p ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hp
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hφp : φ ⟨p, hpH⟩ = 1 := h.actH_eq_one_of_mem_pCoreOf hIU hp
  have hmulφ : φ ⟨a * b * p, h.K₀_le_H hnK⟩ = φ ⟨a, haH⟩ * φ ⟨b, hbH⟩ * φ ⟨p, hpH⟩ := by
    rw [← map_mul, ← map_mul]
    rfl
  have hab : φ ⟨a, haH⟩ * φ ⟨b, hbH⟩ = 1 := by
    rw [hmulφ, hφp, mul_one] at hact
    exact hact
  have hcommφ : ∀ (a' : G) (ha' : a' ∈ K),
      φ ⟨a', hKH ha'⟩ * φ ⟨b, hbH⟩ = φ ⟨b, hbH⟩ * φ ⟨a', hKH ha'⟩ := by
    intro a' ha'
    have hcP : a' * b * a'⁻¹ * b⁻¹ ∈ pCoreOf 2 H :=
      hcomm (Subgroup.commutator_mem_commutator ha' hb)
    have hmemH : a' * b * a'⁻¹ * b⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem (hKH ha') hbH) (H.inv_mem (hKH ha'))) (H.inv_mem hbH)
    have h1 := h.actH_eq_one_of_mem_pCoreOf hIU (x := ⟨_, hmemH⟩) hcP
    have h2 : φ ⟨a' * b * a'⁻¹ * b⁻¹, hmemH⟩ =
        φ ⟨a', hKH ha'⟩ * φ ⟨b, hbH⟩ * (φ ⟨a', hKH ha'⟩)⁻¹ * (φ ⟨b, hbH⟩)⁻¹ := by
      have e : (⟨a' * b * a'⁻¹ * b⁻¹, hmemH⟩ : ↥H) =
          ⟨a', hKH ha'⟩ * ⟨b, hbH⟩ * ⟨a', hKH ha'⟩⁻¹ * ⟨b, hbH⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [h2] at h1
    have h3 : φ ⟨a', hKH ha'⟩ * φ ⟨b, hbH⟩ * (φ ⟨a', hKH ha'⟩)⁻¹ = φ ⟨b, hbH⟩ := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h3
  have hmemL : φ ⟨a, haH⟩ ∈ autIH V₁ I H K := by
    rw [autIH_eq_map h hKH]
    exact ⟨⟨a, haH⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hαinv : φ ⟨a, haH⟩ = (φ ⟨b, hbH⟩)⁻¹ := eq_inv_of_mul_eq_one_left hab
  have hα1 : φ ⟨a, haH⟩ = 1 := by
    have hz : (⟨φ ⟨a, haH⟩, hmemL⟩ : ↥(autIH V₁ I H K)) ∈ Subgroup.center ↥(autIH V₁ I H K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨s, rfl⟩ := toAutI_surjective h I g
      apply Subtype.ext
      show φ ⟨s, hKH s.2⟩ * φ ⟨a, haH⟩ = φ ⟨a, haH⟩ * φ ⟨s, hKH s.2⟩
      rw [hαinv]
      exact (Commute.inv_right (hcommφ s s.2)).eq
    rw [hcen, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  have haP : a ∈ pCoreOf 2 H :=
    mem_pCoreOf_of_mem_K_of_actH_eq_one h hIU hS hne ha hα1
  have hβ1 : φ ⟨b, hbH⟩ = 1 := by
    have := hab
    rw [hα1, one_mul] at this
    exact this
  have hbP : b ∈ pCoreOf 2 H := by
    obtain ⟨a'', ha'', rfl⟩ := hb
    have ha''H : a'' ∈ H := hKH ha''
    have e : (⟨(MulAut.conj t).toMonoidHom a'', hbH⟩ : ↥H) = ⟨t, htH⟩ * ⟨a'', ha''H⟩ * ⟨t, htH⟩⁻¹ :=
      by
        apply Subtype.ext
        simp [MulAut.conj_apply]
    rw [e, map_mul, map_mul, map_inv] at hβ1
    have h4 : φ ⟨a'', ha''H⟩ = 1 := by
      have h5 : φ ⟨t, htH⟩ * φ ⟨a'', ha''H⟩ * (φ ⟨t, htH⟩)⁻¹ = 1 := hβ1
      have h6 := mul_inv_eq_one.mp h5
      simpa using h6
    exact hc t htH a'' (mem_pCoreOf_of_mem_K_of_actH_eq_one h hIU hS hne ha'' h4)
  exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).mul_mem haP hbP) hp

theorem autIH_centralizerMod_eq (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K)
    (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    autIH V₁ I H (centralizerMod (pCoreOf 2 H) H (conjClosure K T)) =
      autIH V₁ I H H ⊓ Subgroup.centralizer
        ((autIH V₁ I H (conjClosure K T) : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H)))) :
          Set (MulAut ↥(tildeOf V₁ (conjClosure I H)))) := by
  have hC₀H : centralizerMod (pCoreOf 2 H) H (conjClosure K T) ≤ H := centralizerMod_le_left _ _ _
  have hPH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hPH' : ∀ {y : G}, y ∈ H → y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := fun hy => hPH hy
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  ext ψ
  rw [autIH_eq_map h hC₀H, Subgroup.mem_inf, autIH_eq_map h le_rfl, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨x, hxH⟩, hxC, rfl⟩
    have hxC' : x ∈ centralizerMod (pCoreOf 2 H) H (conjClosure K T) := Subgroup.mem_subgroupOf.mp hxC
    refine ⟨⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxH, rfl⟩, ?_⟩
    intro g hg
    rw [autIH_eq_map h h.K₀_le_H] at hg
    obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hg
    have hkK : k ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hk
    have hcP : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hxC'.2.2 k hkK
    have hmemH : k * x * k⁻¹ * x⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hkH hxH) (H.inv_mem hkH)) (H.inv_mem hxH)
    have hP' : k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
      have := (pCoreOf 2 H).inv_mem hcP
      have e : (x * k * x⁻¹ * k⁻¹)⁻¹ = k * x * k⁻¹ * x⁻¹ := by group
      rwa [e] at this
    have h1 := h.actH_eq_one_of_mem_pCoreOf hIU (x := ⟨_, hmemH⟩) hP'
    have e : (⟨k * x * k⁻¹ * x⁻¹, hmemH⟩ : ↥H) =
        ⟨k, hkH⟩ * ⟨x, hxH⟩ * ⟨k, hkH⟩⁻¹ * ⟨x, hxH⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  · rintro ⟨⟨⟨x, hxH⟩, -, rfl⟩, hcent⟩
    refine ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    refine ⟨hxH, hPH' hxH, fun k hkK => ?_⟩
    have hkH : k ∈ H := h.K₀_le_H hkK
    have hmemK : φ ⟨k, hkH⟩ ∈ autIH V₁ I H (conjClosure K T) := by
      rw [autIH_eq_map h h.K₀_le_H]
      exact ⟨⟨k, hkH⟩, Subgroup.mem_subgroupOf.mpr hkK, rfl⟩
    have hk' : φ ⟨k, hkH⟩ * φ ⟨x, hxH⟩ = φ ⟨x, hxH⟩ * φ ⟨k, hkH⟩ := hcent _ hmemK
    have hnK : x * k * x⁻¹ * k⁻¹ ∈ conjClosure K T :=
      (conjClosure K T).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (h.K₀_normal hxH) k).mp hkK)
        ((conjClosure K T).inv_mem hkK)
    have hact : φ ⟨x * k * x⁻¹ * k⁻¹, h.K₀_le_H hnK⟩ = 1 := by
      have e' : (⟨x * k * x⁻¹ * k⁻¹, h.K₀_le_H hnK⟩ : ↥H) =
          ⟨x, hxH⟩ * ⟨k, hkH⟩ * ⟨x, hxH⟩⁻¹ * ⟨k, hkH⟩⁻¹ := rfl
      rw [e', map_mul, map_mul, map_mul, map_inv, map_inv, ← hk']
      simp
    exact ker_K₀_le_pCore h hH hA37 hA38 hK hIU hnt hnK hact

theorem five_iii_c_O2 (hO2 : CFSG.Quasithin.H13.T326.D321O2)
    (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (hK : conjClosure K T ≠ K) (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTildeT h hIU) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hC : IsPSL 3 2 1 ↥(autIH V₁ I H K))
    (htop : orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I) ≠ ⊤) :
    Nonempty (↥(oTwoRes (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
        (tildeOf V₁ (conjClosure I H)))) ≃* Multiplicative (ZMod 5)) ∨
      Nonempty (↥(oTwoRes (autOn (tildeOf V₁ (centralizerMod (pCoreOf 2 H) H (conjClosure K T)))
        (tildeOf V₁ (conjClosure I H)))) ≃*
          (Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) := by
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  have hD := d31_of_hyp h hH hIU hV₁I hirr'
  have hnt := hnt_of_irrSec h hIU hirr'.1.2.2.2.1
  have hKI := K₀_le_normalizer_of_isInv h hIU hV₁I hirr'.1.2.1
  obtain ⟨B, hA⟩ := qOff_of_hyp h hIU hV₁I hKI hnt
  obtain ⟨hL38, -, hdata⟩ := five_prelim h hH hK hIU hnt hA37 hA38
  obtain ⟨ht'T, ht'L, hMp, -⟩ := hdata t ht htK
  have hstd : D3Std (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T)
      (autIH V₁ I H K) (subM V₁ (conjClosure I H) I) := ⟨hD, hA.qhat_VT hD.exp, hirr'⟩
  have hqM := hA.qhat_M hD.sylow.1
  have h2 := hO2 _ _ _ _ _ _ hstd _ ht'T ht'L hMp hqM htop hC
  rw [← autIH_centralizerMod_eq h hH hA37 hA38 hK hIU hnt] at h2
  exact nonempty_mulEquiv_five_of_card h2

end Kernel2

end CFSG.Quasithin.RonanF918
