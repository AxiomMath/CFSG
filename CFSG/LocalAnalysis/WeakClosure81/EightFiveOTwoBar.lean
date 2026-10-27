module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] [Finite G]

private theorem commutator_self_le_of_subgroup (K : Subgroup G) : ⁅K, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

private theorem subgroupOf_commutator_eq {K H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K) :
    (⁅H₁, H₂⁆).subgroupOf K = ⁅H₁.subgroupOf K, H₂.subgroupOf K⁆ := by
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h₁,
    Subgroup.map_subgroupOf_eq_of_le h₂,
    Subgroup.map_subgroupOf_eq_of_le
      ((Subgroup.commutator_mono h₁ h₂).trans (commutator_self_le_of_subgroup K))]

private theorem relIndex_eq_card_map_quotient {H C Q : Subgroup G} (hQH : Q ≤ H)
    [hD : (C.subgroupOf H).Normal] :
    C.relIndex Q =
      Nat.card ((Q.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H))) := by
  have hker : (QuotientGroup.mk' (C.subgroupOf H)).ker = C.subgroupOf H :=
    QuotientGroup.ker_mk' (C.subgroupOf H)
  have h1 : (QuotientGroup.mk' (C.subgroupOf H)).ker.relIndex (Q.subgroupOf H) =
      Nat.card ((Q.subgroupOf H).map (QuotientGroup.mk' (C.subgroupOf H))) :=
    Subgroup.relIndex_ker (K := Q.subgroupOf H) (QuotientGroup.mk' (C.subgroupOf H))
  rw [hker] at h1
  rw [← h1]
  exact (Subgroup.relIndex_subgroupOf hQH).symm

private theorem le_normalizer_self {Γ : Type*} [Group Γ] (K : Subgroup Γ) :
    K ≤ Subgroup.normalizer (K : Set Γ) :=
  Subgroup.le_normalizer_iff.mpr fun a ha b hb => K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)

private theorem odd_card_of_nilpotent_normal {Γ : Type*} [Group Γ] [Finite Γ]
    (hO2 : ∀ P : Subgroup Γ, P.Normal → IsPGroup 2 P → P = ⊥)
    {A : Subgroup Γ} [A.Normal] [Group.IsNilpotent ↥A] : Odd (Nat.card A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := ↥A)
  haveI hQchar : (Q : Subgroup ↥A).Characteristic :=
    Sylow.characteristic_of_normal Q (inferInstance : Q.Normal)
  haveI hQxn : ((Q : Subgroup ↥A).map A.subtype).Normal := inferInstance
  have hQx2 : IsPGroup 2 ((Q : Subgroup ↥A).map A.subtype) := Q.isPGroup'.map A.subtype
  have hQbotx := hO2 _ hQxn hQx2
  have hQbot : (Q : Subgroup ↥A) = ⊥ := by
    have h := congrArg (fun X : Subgroup Γ => X.subgroupOf A) hQbotx
    simp only [Subgroup.bot_subgroupOf] at h
    have hQeq : ((Q : Subgroup ↥A).map A.subtype).subgroupOf A = (Q : Subgroup ↥A) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    rwa [hQeq] at h
  have hcard : Nat.card A = (Q : Subgroup ↥A).index := by
    have h := Subgroup.card_mul_index (Q : Subgroup ↥A)
    rw [hQbot, Subgroup.card_bot, one_mul] at h
    simpa [hQbot] using h.symm
  rw [hcard]
  exact Nat.not_even_iff_odd.mp fun hE => Q.not_dvd_index (even_iff_two_dvd.mp hE)

private theorem le_normalizer_centralizer_of_le_normalizer {H E : Subgroup G}
    (hHE : H ≤ Subgroup.normalizer (E : Set G)) :
    H ≤ Subgroup.normalizer (Subgroup.centralizer (E : Set G) : Set G) := by
  have key : ∀ x ∈ H, ∀ c ∈ Subgroup.centralizer (E : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (E : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro e he
    have hmemE : x⁻¹ * e * x ∈ E :=
      ((Subgroup.mem_normalizer_iff''.mp (hHE hx)) e).mp he
    have hc' := hc (x⁻¹ * e * x) hmemE
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [hc']
      _ = (x * c * x⁻¹) * e := by group
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨key h hh c, fun hc => by
    have h' := key h⁻¹ (H.inv_mem hh) (h * c * h⁻¹) hc
    simpa [mul_assoc] using h'⟩

theorem le_centralizer_conjClosure_of_isPGroup {H T E₀ P : Subgroup G}
    (hT : IsSylowIn 2 T H) (hE₀ : E₀ ≤ Subgroup.centralizer (T : Set G))
    (hPH : P ≤ H) (hP : IsPGroup 2 P)
    (hnorm : H ≤ Subgroup.normalizer
      ((P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) : Subgroup G) : Set G)) :
    P ≤ Subgroup.centralizer (conjClosure E₀ H : Set G) := by
  obtain ⟨h, hh, hPhT⟩ := exists_conj_le_of_isSylowTwoOf hT hPH hP
  have hconj_cent : ∀ {A B : Subgroup G} (x : G), A ≤ Subgroup.centralizer (B : Set G) →
      cjSub x A ≤ Subgroup.centralizer (cjSub x B : Set G) := by
    intro A B x hAB
    rw [Subgroup.le_centralizer_iff] at hAB ⊢
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hw' : x⁻¹ * w * x ∈ B := mem_cjSub.mp hw
    have hu' : x⁻¹ * u * x ∈ A := mem_cjSub.mp hu
    have hcomm : (x⁻¹ * u * x) * (x⁻¹ * w * x) = (x⁻¹ * w * x) * (x⁻¹ * u * x) :=
      Subgroup.mem_centralizer_iff.mp (hAB hw') (x⁻¹ * u * x) hu'
    calc u * w = x * ((x⁻¹ * u * x) * (x⁻¹ * w * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * w * x) * (x⁻¹ * u * x)) * x⁻¹ := by rw [hcomm]
      _ = w * u := by group
  have hZT : T ≤ Subgroup.centralizer (E₀ : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hE₀ hz) t ht).symm
  have hPle : P ≤ cjSub h⁻¹ T := by
    have hmono : cjSub h⁻¹ (cjSub h P) ≤ cjSub h⁻¹ T :=
      Subgroup.map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hPhT
    rwa [cjSub_inv_cjSub] at hmono
  have hPcent : P ≤ Subgroup.centralizer (cjSub h⁻¹ E₀ : Set G) :=
    hPle.trans (hconj_cent h⁻¹ hZT)
  have hRcent : P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) ≤
      Subgroup.centralizer (cjSub h⁻¹ E₀ : Set G) := by
    refine sup_le hPcent ?_
    refine le_trans inf_le_right (Subgroup.centralizer_le ?_)
    intro x hx
    change x ∈ cjSub h⁻¹ E₀ at hx
    rw [mem_cjSub] at hx
    have hthis := mem_conjClosure (H.inv_mem hh) hx
    have hx' : h⁻¹ * (h⁻¹⁻¹ * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rwa [hx'] at hthis
  have hRcent_g : ∀ g ∈ H, P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) ≤
      Subgroup.centralizer (cjSub g E₀ : Set G) := by
    intro g hg
    have hgH : g * h ∈ H := H.mul_mem hg hh
    have hRfix : cjSub (g * h) (P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G))) =
        P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) := by
      have hmemnorm : g * h ∈ Subgroup.normalizer
          ((P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) : Subgroup G) : Set G) :=
        hnorm hgH
      simpa [cjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hmemnorm
    have hconj := hconj_cent (g * h) hRcent
    rw [hRfix] at hconj
    have hcj : cjSub (g * h) (cjSub h⁻¹ E₀) = cjSub g E₀ := by
      have hcomp : cjSub (g * h) (cjSub h⁻¹ E₀) = cjSub ((g * h) * h⁻¹) E₀ := by
        ext x
        rw [mem_cjSub, mem_cjSub, mem_cjSub]
        constructor <;> intro hx <;> simpa [mul_assoc] using hx
      rw [hcomp]
      congr 1
      group
    rwa [hcj] at hconj
  have hRE : P ⊔ (H ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G)) ≤
      Subgroup.centralizer (conjClosure E₀ H : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine conjClosure_le fun g hg z hz => ?_
    have hmem : g * z * g⁻¹ ∈ cjSub g E₀ := by
      rw [mem_cjSub]
      rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact (Subgroup.le_centralizer_iff.mp (hRcent_g g hg)) hmem
  exact le_sup_left.trans hRE

theorem le_centralizer_conjClosure_of_two_pow_relIndex {H T E₀ P : Subgroup G}
    (hT : IsSylowIn 2 T H) (hE₀ : E₀ ≤ Subgroup.centralizer (T : Set G))
    (hPH : P ≤ H) (hP : (P.subgroupOf H).Normal)
    (hP2 : ∃ k : ℕ, (Subgroup.centralizer (conjClosure E₀ H : Set G)).relIndex P = 2 ^ k) :
    P ≤ Subgroup.centralizer (conjClosure E₀ H : Set G) := by
  set C := Subgroup.centralizer (conjClosure E₀ H : Set G) with hC
  have hEH : H ≤ Subgroup.normalizer (conjClosure E₀ H : Set G) :=
    le_normalizer_conjClosure E₀ H
  have hHnC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer hEH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ := Sylow.nonempty (p := 2) (G := ↥P)
  set S : Subgroup G := (S₀ : Subgroup ↥P).map P.subtype with hS
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := S₀.isPGroup'.map P.subtype
  have hSsub : S.subgroupOf P = (S₀ : Subgroup ↥P) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSodd : ¬ 2 ∣ S.relIndex P := by
    rw [Subgroup.relIndex, hSsub]
    exact Sylow.not_dvd_index S₀
  have hrel1 : (S ⊔ (P ⊓ C)).relIndex P = 1 := by
    have hR1 : (S ⊔ (P ⊓ C)).relIndex P ∣ S.relIndex P :=
      Subgroup.relIndex_dvd_of_le_left P le_sup_left
    have hR2 : (S ⊔ (P ⊓ C)).relIndex P ∣ (P ⊓ C).relIndex P :=
      Subgroup.relIndex_dvd_of_le_left P le_sup_right
    have hCP : (P ⊓ C).relIndex P = C.relIndex P := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right C P
    obtain ⟨k, hk⟩ := hP2
    have hR2' : (S ⊔ (P ⊓ C)).relIndex P ∣ 2 ^ k := by
      rw [hCP, hk] at hR2
      exact hR2
    have hSodd' : Odd (S.relIndex P) :=
      Nat.not_even_iff_odd.mp fun hE => hSodd (even_iff_two_dvd.mp hE)
    have hcop : Nat.Coprime (S.relIndex P) (2 ^ k) :=
      (Nat.coprime_two_right.mpr hSodd').pow_right k
    exact Nat.eq_one_of_dvd_coprimes hcop hR1 hR2'
  have hPE : P = S ⊔ (P ⊓ C) :=
    le_antisymm (Subgroup.relIndex_eq_one.mp hrel1) (sup_le hSP inf_le_left)
  have hSeq : (S ⊔ (H ⊓ C) : Subgroup G) = P ⊔ (H ⊓ C) := by
    rw [hPE, sup_assoc, sup_eq_right.mpr (inf_le_inf hPH le_rfl)]
  have hHnorm : H ≤ Subgroup.normalizer
      ((S ⊔ (H ⊓ C) : Subgroup G) : Set G) := by
    have h1 : H ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal_subgroupOf hPH
    have h2 : H ≤ Subgroup.normalizer ((H ⊓ C : Subgroup G) : Set G) :=
      le_trans (le_inf (le_normalizer_self H) hHnC)
        (Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := C))
    have h3 : H ≤ Subgroup.normalizer ((P ⊔ (H ⊓ C) : Subgroup G) : Set G) :=
      le_trans (le_inf h1 h2) (Subgroup.inf_normalizer_le_normalizer_sup P (H ⊓ C))
    rw [hSeq]
    exact h3
  have hSC : S ≤ C :=
    le_centralizer_conjClosure_of_isPGroup (P := S) hT hE₀ (hSP.trans hPH) hS2 hHnorm
  rw [hPE]
  exact sup_le hSC inf_le_right

private theorem exists_normal_sylow_two_of_le_center_of_index {Γ : Type*} [Group Γ] [Finite Γ]
    {Z : Subgroup Γ} [hZnorm : Z.Normal] (hZ : Z ≤ Subgroup.center Γ)
    (h2 : ∃ m, Z.index = 2 ^ m) :
    ∃ S : Sylow 2 Γ, S.Normal ∧ (Z ⊔ (S : Subgroup Γ) = ⊤) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := Γ)
  have htop : Z ⊔ (S : Subgroup Γ) = ⊤ := by
    apply Subgroup.index_eq_one.mp
    have h1 : (Z ⊔ (S : Subgroup Γ)).index ∣ Z.index :=
      Subgroup.index_dvd_of_le le_sup_left
    have h2' : (Z ⊔ (S : Subgroup Γ)).index ∣ S.index :=
      Subgroup.index_dvd_of_le le_sup_right
    obtain ⟨m, hm⟩ := h2
    have h1' : (Z ⊔ (S : Subgroup Γ)).index ∣ 2 ^ m := by
      rw [← hm]
      exact h1
    have hSodd : Odd S.index :=
      Nat.not_even_iff_odd.mp fun hE => S.not_dvd_index (even_iff_two_dvd.mp hE)
    have hcop : Nat.Coprime S.index (2 ^ m) :=
      (Nat.coprime_two_right.mpr hSodd).pow_right m
    exact Nat.eq_one_of_dvd_coprimes hcop h2' h1'
  have hle : Z ⊔ (S : Subgroup Γ) ≤ Subgroup.normalizer (S : Set Γ) :=
    sup_le (hZ.trans (Subgroup.center_le_normalizer (s := (S : Set Γ))))
      (le_normalizer_self (S : Subgroup Γ))
  have hnorm : Subgroup.normalizer (S : Set Γ) = ⊤ :=
    le_antisymm le_top (by rw [← htop]; exact hle)
  exact ⟨S, Subgroup.normalizer_eq_top_iff.mp hnorm, htop⟩

theorem centralizer_le_of_normal_of_two_pow_index {X : Type*} [Group X] [Finite X]
    (hX : ∀ P : Subgroup X, P.Normal → IsPGroup 2 P → P = ⊥)
    {N : Subgroup X} [N.Normal] (hN : ∃ k : ℕ, N.index = 2 ^ k) :
    Subgroup.centralizer (N : Set X) ≤ N := by
  set C := Subgroup.centralizer (N : Set X) with hC
  haveI hCnorm : C.Normal := Subgroup.normal_centralizer
  set Z : Subgroup X := C ⊓ N with hZ
  haveI hZnorm : Z.Normal := by rw [hZ]; infer_instance
  have hZcenter : (Z.subgroupOf C) ≤ Subgroup.center ↥C := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hzN : z.1 ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).2
    exact (Subgroup.mem_centralizer_iff.mp c.2 z.1 hzN).symm
  have hidx : ∃ m, (Z.subgroupOf C).index = 2 ^ m := by
    obtain ⟨k, hk⟩ := hN
    have hZeq : Z.subgroupOf C = N.subgroupOf C := by
      rw [hZ]
      exact Subgroup.inf_subgroupOf_left N C
    have hdvd : (Z.subgroupOf C).index ∣ N.index := by
      rw [hZeq]
      change N.relIndex C ∣ N.index
      have hker : N.relIndex C = Nat.card (C.map (QuotientGroup.mk' N)) := by
        have h := Subgroup.relIndex_ker (f := QuotientGroup.mk' N) (K := C)
        rw [QuotientGroup.ker_mk'] at h
        exact h
      rw [hker]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hk ▸ hdvd)
    exact ⟨m, hm⟩
  obtain ⟨S, hSnorm, hStop⟩ := exists_normal_sylow_two_of_le_center_of_index hZcenter hidx
  haveI hSchar : (S : Subgroup ↥C).Characteristic := Sylow.characteristic_of_normal S hSnorm
  haveI hSxn : ((S : Subgroup ↥C).map C.subtype).Normal := inferInstance
  have hSx2 : IsPGroup 2 ((S : Subgroup ↥C).map C.subtype) := S.isPGroup'.map C.subtype
  have hSxbot : (S : Subgroup ↥C) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective ((S : Subgroup ↥C)) C.subtype_injective).mp
      (hX _ hSxn hSx2)
  have hZtop : Z.subgroupOf C = ⊤ := by
    have := hStop
    rw [hSxbot, sup_bot_eq] at this
    exact this
  intro c hc
  have hmem : (⟨c, hc⟩ : ↥C) ∈ Z.subgroupOf C := by rw [hZtop]; exact Subgroup.mem_top _
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2

theorem eq_bot_of_normal_isPGroup_two_quot_centralizer {H T E₀ : Subgroup G}
    (hT : IsSylowIn 2 T H) (hE₀ : E₀ ≤ Subgroup.centralizer (T : Set G))
    [hD : ((Subgroup.centralizer (conjClosure E₀ H : Set G)).subgroupOf H).Normal] :
    ∀ P : Subgroup (↥H ⧸ (Subgroup.centralizer (conjClosure E₀ H : Set G)).subgroupOf H),
      P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hPn hP2
  set C := Subgroup.centralizer (conjClosure E₀ H : Set G) with hC
  set D' : Subgroup ↥H := C.subgroupOf H with hD'
  let π : ↥H →* (↥H ⧸ D') := QuotientGroup.mk' D'
  set Pg : Subgroup G := (P.comap π).map H.subtype with hPg
  have hPgH : Pg ≤ H := Subgroup.map_subtype_le _
  have hPgsub : Pg.subgroupOf H = P.comap π := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hPgnorm : (Pg.subgroupOf H).Normal := by
    rw [hPgsub]
    exact Subgroup.Normal.comap hPn π
  have hrel : C.relIndex Pg = Nat.card P := by
    rw [relIndex_eq_card_map_quotient (C := C) (H := H) hPgH, hPgsub,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D') P]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hP2' : ∃ k, C.relIndex Pg = 2 ^ k := ⟨k, by rw [hrel, hk]⟩
  have hle := le_centralizer_conjClosure_of_two_pow_relIndex hT hE₀ hPgH hPgnorm hP2'
  have hleD : P.comap π ≤ D' := by
    intro x hx
    exact hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hPd : P = (P.comap π).map π :=
    (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D') P).symm
  rw [hPd, eq_bot_iff]
  calc (P.comap π).map π ≤ D'.map π := Subgroup.map_mono hleD
    _ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem odd_relIndex_of_commutator_le {H T E₀ K Y : Subgroup G}
    (hT : IsSylowIn 2 T H) (hE₀ : E₀ ≤ Subgroup.centralizer (T : Set G))
    (hKH : (K.subgroupOf H).Normal) (hKT : H = K ⊔ T)
    (hYH : Y ≤ H) (hYK : ⁅Y, K⁆ ≤ Subgroup.centralizer (conjClosure E₀ H : Set G)) :
    Odd ((Subgroup.centralizer (conjClosure E₀ H : Set G)).relIndex Y) := by
  set E := conjClosure E₀ H with hE
  set C := Subgroup.centralizer (E : Set G) with hC
  have hEH : H ≤ Subgroup.normalizer (E : Set G) := le_normalizer_conjClosure E₀ H
  have hHnC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizer_of_le_normalizer hEH
  have hKle : K ≤ H := by rw [hKT]; exact le_sup_left
  have hTle : T ≤ H := by rw [hKT]; exact le_sup_right
  set D' : Subgroup ↥H := C.subgroupOf H with hD'
  haveI hD'norm : D'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHnC
  let π : ↥H →* (↥H ⧸ D') := QuotientGroup.mk' D'
  have hO2X : ∀ P : Subgroup (↥H ⧸ D'), P.Normal → IsPGroup 2 P → P = ⊥ :=
    eq_bot_of_normal_isPGroup_two_quot_centralizer (H := H) (T := T) (E₀ := E₀)
      (hD := hD'norm) hT hE₀
  set Kbar : Subgroup (↥H ⧸ D') := (K.subgroupOf H).map π with hKbar
  haveI hKbarnorm : Kbar.Normal := by
    rw [hKbar]
    exact Subgroup.Normal.map hKH π (QuotientGroup.mk'_surjective D')
  have hTsub2 : IsPGroup 2 ((T.subgroupOf H).map π) :=
    (hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm).map π
  have hKT_sub : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKle hTle, hKT, Subgroup.subgroupOf_self]
  have hmap_top : ((K.subgroupOf H) ⊔ (T.subgroupOf H)).map π = ⊤ := by
    rw [hKT_sub]
    exact Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective D')
  have htop : (T.subgroupOf H).map π ⊔ Kbar = ⊤ := by
    have h := hmap_top
    rw [Subgroup.map_sup] at h
    rw [hKbar, sup_comm]
    exact h
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hTsub2
  have hidx : Kbar.index = Kbar.relIndex ((T.subgroupOf H).map π) := by
    rw [← Subgroup.relIndex_sup_right (H := (T.subgroupOf H).map π) (K := Kbar), htop,
      Subgroup.relIndex_top_right]
  have hdvd : Kbar.index ∣ Nat.card ((T.subgroupOf H).map π) := by
    rw [hidx]
    exact Subgroup.relIndex_dvd_card (H := Kbar) (K := (T.subgroupOf H).map π)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hj ▸ hdvd)
  have hKidx : ∃ k, Kbar.index = 2 ^ k := ⟨m, hm⟩
  set Ybar : Subgroup (↥H ⧸ D') := (Y.subgroupOf H).map π with hYbar
  have hYcent : Ybar ≤ Subgroup.centralizer (Kbar : Set (↥H ⧸ D')) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [hYbar, hKbar, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    rw [show π.ker = C.subgroupOf H from QuotientGroup.ker_mk' D']
    rw [← subgroupOf_commutator_eq hYH hKle]
    exact Subgroup.subgroupOf_mono H hYK
  have hCK : Subgroup.centralizer (Kbar : Set (↥H ⧸ D')) ≤ Kbar :=
    centralizer_le_of_normal_of_two_pow_index hO2X hKidx
  set Z0 : Subgroup (↥H ⧸ D') := Kbar ⊓ Subgroup.centralizer (Kbar : Set (↥H ⧸ D')) with hZ0
  have hYle : Ybar ≤ Z0 := le_inf (hYcent.trans hCK) hYcent
  haveI hZnorm : Z0.Normal := by
    rw [hZ0]
    exact Subgroup.normal_inf_normal _ _
  haveI hZnil : Group.IsNilpotent ↥Z0 := by
    haveI : IsMulCommutative ↥Z0 :=
      IsMulCommutative.of_comm fun a b =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp b.2.2 a.1 a.2.1)
    infer_instance
  have hOddZ : Odd (Nat.card Z0) := odd_card_of_nilpotent_normal hO2X
  have hYodd : Odd (Nat.card Ybar) :=
    Nat.not_even_iff_odd.mp fun hE' =>
      hOddZ.not_two_dvd_nat
        (dvd_trans (even_iff_two_dvd.mp hE') (Subgroup.card_dvd_of_le hYle))
  rw [relIndex_eq_card_map_quotient (C := C) (H := H) hYH]
  exact hYodd

theorem eq_bot_of_commutator_le_of_isPGroup {H T E₀ K Y : Subgroup G}
    (hT : IsSylowIn 2 T H) (hE₀ : E₀ ≤ Subgroup.centralizer (T : Set G))
    (hKH : (K.subgroupOf H).Normal) (hKT : H = K ⊔ T)
    (hYH : Y ≤ H) (hY : IsPGroup 2 Y)
    (hYC : Y ⊓ Subgroup.centralizer (conjClosure E₀ H : Set G) = ⊥)
    (hYK : ⁅Y, K⁆ ≤ Subgroup.centralizer (conjClosure E₀ H : Set G)) :
    Y = ⊥ := by
  have hodd := odd_relIndex_of_commutator_le hT hE₀ hKH hKT hYH hYK
  have hCY : (Subgroup.centralizer (conjClosure E₀ H : Set G)).relIndex Y = Nat.card Y := by
    have hbot : (Subgroup.centralizer (conjClosure E₀ H : Set G)).subgroupOf Y = ⊥ := by
      rw [← Subgroup.inf_subgroupOf_left (Subgroup.centralizer (conjClosure E₀ H : Set G)) Y,
        hYC, Subgroup.bot_subgroupOf]
    change ((Subgroup.centralizer (conjClosure E₀ H : Set G)).subgroupOf Y).index = Nat.card Y
    rw [hbot, Subgroup.index_bot]
  rw [hCY] at hodd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY
  rw [hn] at hodd
  have hn0 : n = 0 := by
    by_contra h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
    exact hodd.not_two_dvd_nat ⟨2 ^ k, by rw [pow_succ]; ring⟩
  rw [hn0, pow_zero] at hn
  exact Subgroup.card_eq_one.mp hn

end CFSG.LocalAnalysis.WeakClosure81

end
