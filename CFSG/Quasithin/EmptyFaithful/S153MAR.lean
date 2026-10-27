module

public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace S153M

private theorem centerOf_le_genFitting {Ω : Type} [Group Ω] (J : Subgroup Ω) :
    centerOf J ≤ quasithinGenFitting J := by
  refine le_sup_of_le_left (le_sSup ⟨fun x hx => hx.1, ⟨fun n hn g => ?_⟩, ?_⟩)
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := Subgroup.mem_centralizer_iff.mp hn.2 (g : Ω) g.2
    refine ⟨J.mul_mem (J.mul_mem g.2 hn.1) (J.inv_mem g.2), ?_⟩
    have e : (g : Ω) * (n : Ω) * (g : Ω)⁻¹ = n := by rw [h1, mul_inv_cancel_right]
    simpa [e] using hn.2
  · let _ : CommGroup ↥(centerOf J) :=
      { (inferInstance : Group ↥(centerOf J)) with
        mul_comm := fun a b => Subtype.ext
          ((Subgroup.mem_centralizer_iff.mp b.2.2 (a : Ω) a.2.1)) }
    exact CommGroup.isNilpotent

private theorem isNilpotent_of_central_two_quot {Ω : Type*} [Group Ω] [Finite Ω]
    {N A : Subgroup Ω} (hc : ∀ a ∈ A, ∀ n ∈ N, a * n = n * a)
    (h2 : ∀ n ∈ N, ∃ e : ℕ, n ^ 2 ^ e ∈ A) : Group.IsNilpotent ↥N := by
  have hAn : (A.subgroupOf N).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    have h1 := hc a ha g g.2
    have e : (g : Ω) * a * (g : Ω)⁻¹ = a := by
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    show (g : Ω) * a * (g : Ω)⁻¹ ∈ A
    rw [e]
    exact ha
  have hcen : (QuotientGroup.mk' (A.subgroupOf N)).ker ≤ Subgroup.center ↥N := by
    rw [QuotientGroup.ker_mk']
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    rw [Subgroup.mem_subgroupOf] at ha
    exact Subtype.ext (hc a ha g g.2).symm
  have hP : IsPGroup 2 (↥N ⧸ A.subgroupOf N) := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := h2 n n.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using he
  have : Group.IsNilpotent (↥N ⧸ A.subgroupOf N) := hP.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (A.subgroupOf N)) hcen

private theorem ar_core {H : Type} [Group H] [Finite H] {V : Type} [CommGroup V] [Finite V]
    (ρ : H →* MulAut V) (K : Subgroup H) [K.Normal]
    (hq : CFSG.Open.IsQuasisimple ↥K) (hO2 : CFSG.pCore 2 H = ⊥)
    (h2 : ∀ y : H, ∃ e : ℕ, y ^ 2 ^ e ∈ K) (hnt : ¬ K ≤ ρ.ker) :
    CFSG.IsQuasisimple ↥(K.map ρ) ∧ K.map ρ ≤ ρ.range ∧
      (∀ x ∈ ρ.range, ∀ l ∈ K.map ρ, x * l * x⁻¹ ∈ K.map ρ) ∧
      (∀ x ∈ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ K.map ρ) ∧ pCoreOf 2 ρ.range = ⊥ := by
  have hrange : (ρ.comp K.subtype).range = K.map ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : (ρ.comp K.subtype).ker ≠ ⊤ := by
    intro h
    apply hnt
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ (ρ.comp K.subtype).ker := by rw [h]; trivial
    exact this
  have hL : CFSG.Open.IsQuasisimple ↥(K.map ρ) := by
    rw [← hrange]
    exact CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hq _ hker
  have hLle : K.map ρ ≤ ρ.range := Subgroup.map_le_range ρ K
  have hLn : ∀ x ∈ ρ.range, ∀ l ∈ K.map ρ, x * l * x⁻¹ ∈ K.map ρ := by
    rintro _ ⟨h, rfl⟩ _ ⟨k, hk, rfl⟩
    refine ⟨h * k * h⁻¹, (inferInstance : K.Normal).conj_mem k hk h, by simp⟩
  have hL2 : ∀ x ∈ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ K.map ρ := by
    rintro _ ⟨h, rfl⟩
    obtain ⟨e, he⟩ := h2 h
    exact ⟨e, by rw [← map_pow]; exact Subgroup.mem_map_of_mem _ he⟩
  refine ⟨B1Red.isQuasisimple_of_open hL, hLle, hLn, hL2, ?_⟩
  set X := ρ.range with hX
  set L := K.map ρ with hLdef
  set R := pCoreOf 2 X with hR
  have hR2 : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
  have hRX : R ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hRn : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hx r hr =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx) r).mp hr
  have hLR : ¬ L ≤ R := by
    intro hLR
    have hnil : Group.IsNilpotent ↥L := (hR2.to_le hLR).isNilpotent
    have : Group.IsPerfect ↥L := ⟨hL.1⟩
    have : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hL
    exact Group.IsPerfect.not_isNilpotent ↥L hnil
  set M : Subgroup H := R.comap ρ with hM
  have hMn : ∀ h : H, ∀ m ∈ M, h * m * h⁻¹ ∈ M := by
    intro h m hm
    have hm' : ρ m ∈ R := hm
    show ρ (h * m * h⁻¹) ∈ R
    rw [map_mul, map_mul, map_inv]
    exact hRn (ρ h) ⟨h, rfl⟩ (ρ m) hm'
  have hKM : ¬ K ≤ M := by
    intro hKM
    apply hLR
    rintro _ ⟨k, hk, rfl⟩
    exact hKM hk
  have hcomm : ∀ m ∈ M, ∀ k ∈ K, m * k = k * m :=
    B1Red.commute_of_normal_not_le hq
      (fun n _ k hk => (inferInstance : K.Normal).conj_mem k hk n)
      (fun k _ m hm => hMn k m hm) hKM
  set C : Subgroup H := Subgroup.centralizer (K : Set H) with hC
  have hMC : M ≤ C := fun m hm => Subgroup.mem_centralizer_iff.2 fun k hk => (hcomm m hm k hk).symm
  have hCn : ∀ y ∈ (⊤ : Subgroup H), ∀ x ∈ C, y * x * y⁻¹ ∈ C := by
    intro y _ x hx
    refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
    have h1 : (y⁻¹ * k * y⁻¹⁻¹) ∈ K := (inferInstance : K.Normal).conj_mem k hk y⁻¹
    have h2' := Subgroup.mem_centralizer_iff.1 hx _ h1
    calc k * (y * x * y⁻¹) = y * ((y⁻¹ * k * y⁻¹⁻¹) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * k * y⁻¹⁻¹)) * y⁻¹ := by rw [h2']
      _ = y * x * y⁻¹ * k := by group
  have hCnil : Group.IsNilpotent ↥C :=
    isNilpotent_of_central_two_quot (A := K ⊓ C)
      (fun a ha n hn => Subgroup.mem_centralizer_iff.1 hn a ha.1)
      (fun n hn => by
        obtain ⟨e, he⟩ := h2 n
        exact ⟨e, he, C.pow_mem hn _⟩)
  have hO2' : pCoreOf 2 (⊤ : Subgroup H) = ⊥ := by
    have hP2 : IsPGroup 2 ↥(pCoreOf 2 (⊤ : Subgroup H)) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
    have hPn : (pCoreOf 2 (⊤ : Subgroup H)).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤)
    have : pCoreOf 2 (⊤ : Subgroup H) ≤ CFSG.pCore 2 H := le_sSup ⟨hPn, hP2⟩
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hodd := B1Red.odd_orderOf_of_nilpotent_normal (Y := ⊤) le_top hCn hO2'
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨m, rfl⟩ := hRX hr
  have hmM : m ∈ M := hr
  have hdvd : orderOf (ρ m) ∣ orderOf m := orderOf_map_dvd ρ m
  have hoddr : Odd (orderOf (ρ m)) := Odd.of_dvd_nat (hodd m (hMC hmM)) hdvd
  obtain ⟨k, hk⟩ := hR2 ⟨ρ m, hr⟩
  have hk' : ρ m ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd2 : orderOf (ρ m) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf (ρ m)) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hoddr)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd2))

private theorem pCore_map_le_pCore {Hg : Type} [Group Hg] (Kg : Subgroup Hg) [Kg.Normal] :
    (CFSG.pCore 2 ↥Kg).map Kg.subtype ≤ CFSG.pCore 2 Hg := by
  refine le_sSup ⟨?_, (CFSG.pCore_isPGroup (p := 2) (G := ↥Kg)).map Kg.subtype⟩
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ Subgroup.normalizer (Kg : Set Hg) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    trivial
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Kg) (CFSG.pCore 2 ↥Kg) hg) n).mp hn

private theorem pCore_subgroupOf_le {Hg : Type} [Group Hg] (Kg : Subgroup Hg) [Kg.Normal] :
    (CFSG.pCore 2 Hg).subgroupOf Kg ≤ CFSG.pCore 2 ↥Kg :=
  le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := 2) (G := Hg)).comap_subtype⟩

private theorem pCore_quotient_pCore_eq_bot {Hg : Type} [Group Hg] :
    CFSG.pCore 2 (Hg ⧸ CFSG.pCore 2 Hg) = ⊥ := by
  set Q := CFSG.pCore 2 Hg with hQ
  set O := CFSG.pCore 2 (Hg ⧸ Q) with hO
  set π := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  have hK : IsPGroup 2 ↥(O.comap π) := by
    refine (CFSG.pCore_isPGroup (p := 2) (G := Hg ⧸ Q)).comap_of_ker_isPGroup π ?_
    rw [hπ, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := Hg)
  have hKn : (O.comap π).Normal := (inferInstance : O.Normal).comap π
  have hKQ : O.comap π ≤ Q := le_sSup ⟨hKn, hK⟩
  rw [eq_bot_iff]
  calc O = (O.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπs O).symm
    _ ≤ Q.map π := Subgroup.map_mono hKQ
    _ = ⊥ := QuotientGroup.map_mk'_self Q

theorem ar_facts {Hg : Type} [Group Hg] [Finite Hg] {V : Type} [CommGroup V] [Finite V]
    (ρ : Hg →* MulAut V) (Kg : Subgroup Hg) [Kg.Normal]
    (hq : CFSG.IsQuasisimple (↥Kg ⧸ CFSG.pCore 2 ↥Kg))
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker) (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ Kg)
    (hnt : ¬ Kg ≤ ρ.ker) :
    CFSG.IsQuasisimple ↥(Kg.map ρ) ∧ Kg.map ρ ≤ ρ.range ∧
      (∀ x ∈ ρ.range, ∀ l ∈ Kg.map ρ, x * l * x⁻¹ ∈ Kg.map ρ) ∧
      (∀ x ∈ ρ.range, ∃ e : ℕ, x ^ 2 ^ e ∈ Kg.map ρ) ∧ pCoreOf 2 ρ.range = ⊥ := by
  set Q : Subgroup Hg := CFSG.pCore 2 Hg with hQdef
  set Z : Subgroup ↥Kg := CFSG.pCore 2 ↥Kg with hZdef
  set π : Hg →* Hg ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q
  set ρ' : (Hg ⧸ Q) →* MulAut V := QuotientGroup.lift Q ρ hQ with hρ'
  set K' : Subgroup (Hg ⧸ Q) := Kg.map π with hK'
  have : K'.Normal := Subgroup.Normal.map inferInstance π hπs
  have hZle : Z ≤ (π.comp Kg.subtype).ker := by
    intro z hz
    have h1 : (z : Hg) ∈ Q := pCore_map_le_pCore Kg ⟨z, hz, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 h1
  set θ : (↥Kg ⧸ Z) →* (Hg ⧸ Q) := QuotientGroup.lift Z (π.comp Kg.subtype) hZle with hθ
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro q hq1
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : (k : Hg) ∈ Q := (QuotientGroup.eq_one_iff _).1 hq1
    exact (QuotientGroup.eq_one_iff _).2 (pCore_subgroupOf_le Kg h1)
  have hθrange : θ.range = K' := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨QuotientGroup.mk ⟨k, hk⟩, rfl⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K' := by
    refine CFSG.ComponentClassification.Components.quasisimple_of_equiv ?_
      (B1Red.isQuasisimple_to_open hq)
    exact ((MulEquiv.subgroupCongr hθrange.symm).trans (MonoidHom.ofInjective hθinj).symm)
  have hO2 : CFSG.pCore 2 (Hg ⧸ Q) = ⊥ := pCore_quotient_pCore_eq_bot
  have h2' : ∀ y : Hg ⧸ Q, ∃ e : ℕ, y ^ 2 ^ e ∈ K' := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨e, he⟩ := h2 y
    exact ⟨e, by rw [← QuotientGroup.mk_pow]; exact Subgroup.mem_map_of_mem π he⟩
  have hnt' : ¬ K' ≤ ρ'.ker := by
    intro h
    apply hnt
    intro k hk
    exact h (Subgroup.mem_map_of_mem π hk)
  have hmap : K'.map ρ' = Kg.map ρ := by
    rw [hK', Subgroup.map_map]
    rfl
  have hrange : ρ'.range = ρ.range := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨π h, rfl⟩
  have := ar_core ρ' K' hKq hO2 h2' hnt'
  rw [hmap, hrange] at this
  exact this

theorem le_ffJ_of_ffModule {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {X L : Subgroup (MulAut V)} (hLX : L ≤ X)
    (hn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L)
    (hq : CFSG.IsQuasisimple ↥L) (hS : SQTKGroup ↥L) (hO2 : pCoreOf 2 X = ⊥)
    (hFF : IsFFModule X) : L ≤ ffJ X ∧ B51Hyp (ffJ X) L := by
  set J := ffJ X with hJ
  have hLo : CFSG.Open.IsQuasisimple ↥L := B1Red.isQuasisimple_to_open hq
  have hJX : J ≤ X := B6.ffJ_le X
  have hXJ : ∀ x ∈ X, ∀ j ∈ J, x * j * x⁻¹ ∈ J := fun x hx j hj =>
    (Subgroup.mem_normalizer_iff.mp (B6.le_normalizer_ffJ X hx) j).mp hj
  have hJn : (J.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J X hJX hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  have hJ0 : J ≠ ⊥ := InternalSec.ffJ_ne_bot_of_isFFModule hV hFF
  have hLJ : L ≤ J := by
    by_contra hLJ
    have hcomm := B1Red.commute_of_normal_not_le hLo
      (fun n hn' l hl => hn n (hJX hn') l hl)
      (fun l hl n hn' => hXJ l (hLX hl) n hn') hLJ
    have hnil : Group.IsNilpotent ↥J :=
      isNilpotent_of_central_two_quot (A := L ⊓ J)
        (fun a ha n hn' => (hcomm n hn' a ha.1).symm)
        (fun n hn' => by
          obtain ⟨e, he⟩ := h2 n (hJX hn')
          exact ⟨e, he, J.pow_mem hn' _⟩)
    have hodd := B1Red.odd_orderOf_of_nilpotent_normal hJX hXJ hO2
    refine hJ0 (le_bot_iff.1 ?_)
    refine iSup₂_le fun A hA a ha => ?_
    have ha2 : a ^ 2 = 1 := hA.2.2.1.2 a ha
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one ha2
    have hodd' := hodd a (B6.le_ffJ hA ha)
    have hcop : Nat.Coprime (orderOf a) 2 := Nat.coprime_two_right.2 hodd'
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd))
  have hF : quasithinGenFitting J = L :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hLJ (fun y hy l hl => hn y (hJX hy) l hl)
      hLo (fun y hy => h2 y (hJX hy)) hQ
  have hZ : centerOf J ≤ L := hF ▸ centerOf_le_genFitting J
  exact ⟨hLJ, ⟨by rw [hF, sup_eq_left.2 hZ], hq, hS, hLJ, hQ, (InternalSec.ffJ_ffJ _).symm⟩⟩

end S153M

end CFSG.Quasithin
