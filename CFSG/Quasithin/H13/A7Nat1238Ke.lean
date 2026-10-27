module

public import CFSG.Quasithin.H13.A7Nat1238Setup
public import CFSG.Quasithin.H13.A7Nat1236Comp
public import CFSG.Quasithin.Vol2.Ch1Nine
public import CFSG.Quasithin.H13.A7CentralCoverGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

abbrev Kv (hyp : Hyp1223 G T L V) (v : G) : Subgroup G := perfectCore (hyp.Lv v)

theorem eq_top_of_perfect_of_isPGroup {X : Subgroup G} (hX : ⁅X, X⁆ = X) (N : Subgroup ↥X)
    [N.Normal] (hN : IsPGroup 2 (↥X ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect ↥X := (Subgroup.isPerfect_iff).2 hX
  have hq : Group.IsPerfect (↥X ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  by_contra hne
  have hnt : Nontrivial (↥X ⧸ N) := QuotientGroup.nontrivial_iff.2 hne
  have : Finite (↥X ⧸ N) := inferInstance
  have hnil : Group.IsNilpotent (↥X ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isSolvable (G := ↥X ⧸ N) inferInstance

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_centralizer (h : A7NatPre T L V ψ)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {x y : G} (hxL : x ∈ L)
    (hxV : x ∈ centralizer (V : Set G)) (hyL : y ∈ L) :
    x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set lam := natLam h.L_le h.Lact with hlam
  have hlams := natLam_surjective h.L_le h.Lact h.Lonto
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hF1 : CFSG.pCore 2 ↥L ≤ lam.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have hN : ((CFSG.pCore 2 ↥L).map lam).Normal := CFSG.pCore_normal.map lam hlams
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hA7s _ hN with h1 | h1
    · exact h1
    · exfalso
      have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).map lam) := CFSG.pCore_isPGroup.map lam
      rw [h1] at h2
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
      rw [Subgroup.card_top, nat_card_alternating_seven] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  set lam' : (↥L ⧸ CFSG.pCore 2 ↥L) →* alternatingGroup (Fin 7) :=
    QuotientGroup.lift _ lam hF1 with hlam'
  have hlam's : Function.Surjective lam' := fun a => by
    obtain ⟨l, rfl⟩ := hlams a
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hK : lam'.ker ≤ center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq lam'.normal_ker with h1 | h1
    · exfalso
      have h2 : ∀ a, a = (1 : alternatingGroup (Fin 7)) := by
        intro a
        obtain ⟨z, rfl⟩ := hlam's a
        exact (MonoidHom.mem_ker).1 (h1 ▸ mem_top z)
      have h3 : Nat.card (alternatingGroup (Fin 7)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (h2 a).trans (h2 b).symm⟩, inferInstance⟩
      rw [nat_card_alternating_seven] at h3
      norm_num at h3
    · exact h1
  have hxk : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ lam'.ker := by
    rw [MonoidHom.mem_ker]
    exact (natLam_eq_one_iff h.L_le h.Lact ⟨x, hxL⟩).2 hxV
  have hc := mem_center_iff.1 (hK hxk) (QuotientGroup.mk ⟨y, hyL⟩)
  have h1 : (⟨x, hxL⟩ : ↥L) * ⟨y, hyL⟩ * (⟨x, hxL⟩ : ↥L)⁻¹ * (⟨y, hyL⟩ : ↥L)⁻¹ ∈
      CFSG.pCore 2 ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hc]
    group
  rw [pCoreOf_eq_map_cfsgPCore]
  exact ⟨_, h1, rfl⟩

theorem center_altFive : center altFive = ⊥ := by
  have hs := isSimpleGroup_altFive
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs (center altFive) inferInstance with
    h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := altFive_nonabelian
    exact hab (mem_center_iff.1 (h ▸ mem_top b) a)

section Ke

variable (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecFS)

include hyp in
theorem Kv_le_Lv (v : G) : Kv hyp v ≤ hyp.Lv v := perfectCore_le _

include hyp in
theorem Kv_le_L (v : G) : Kv hyp v ≤ L :=
  (perfectCore_le _).trans ((oTwoUpper_le _).trans inf_le_left)

include hyp in
theorem Kv_le_centralizer (v : G) : Kv hyp v ≤ centralizer ({v} : Set G) :=
  (perfectCore_le _).trans ((oTwoUpper_le _).trans inf_le_right)

include hyp in
theorem Kv_perfect (v : G) : ⁅Kv hyp v, Kv hyp v⁆ = Kv hyp v := perfectCore_perfect _

theorem T_le_normalizer_Kv (h1225 : Stmt12_2_5) {v : G} (hvV : v ∈ V) (hv1 : v ≠ 1)
    (hvZ : v ∈ quasithinOmegaOneCenter T) : T ≤ normalizer (Kv hyp v : Set G) := by
  obtain ⟨-, hMeN, -, -, -⟩ := h1225 G T L V hyp v hvV hv1
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ hyp.Gv v := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hvZ) t ht))
  exact ((le_inf hyp.normalizes hTe).trans hMeN).trans (normalizer_le_normalizer_perfectCore _)

include he in
theorem natLam_map_Kv :
    ((Kv hyp e).subgroupOf L).map (natLam h.L_le h.Lact) = altFive :=
  natLam_map_Ke_two h.L_le h.Lact h.Lonto he

include he in
theorem exists_mem_Kv_natLam {σ : alternatingGroup (Fin 7)} (hσ : σ ∈ altFive) :
    ∃ k : L, (k : G) ∈ Kv hyp e ∧ natLam h.L_le h.Lact k = σ := by
  rw [← natLam_map_Kv hyp h he] at hσ
  obtain ⟨k, hk, rfl⟩ := hσ
  exact ⟨k, hk, rfl⟩

omit [Finite G] in
theorem vec_commutator_natLam (h : A7NatPre T L V ψ) (x : V) (l : L) :
    ∃ hc : (x : G) * l * (x : G)⁻¹ * (l : G)⁻¹ ∈ V,
      vec ψ ⟨_, hc⟩ = vec ψ x + permAct7 (natLam h.L_le h.Lact l : Perm (Fin 7)) (vec ψ x) := by
  have hlV := h.L_le l.2
  have hy : (l : G) * (x : G)⁻¹ * (l : G)⁻¹ ∈ V :=
    (mem_normalizer_iff.1 hlV _).1 (V.inv_mem x.2)
  have hc : (x : G) * l * (x : G)⁻¹ * (l : G)⁻¹ ∈ V := by
    have := V.mul_mem x.2 hy
    rwa [show (x : G) * ((l : G) * (x : G)⁻¹ * (l : G)⁻¹) =
      (x : G) * l * (x : G)⁻¹ * (l : G)⁻¹ by group] at this
  refine ⟨hc, ?_⟩
  have h1 : (⟨_, hc⟩ : V) = x * ⟨_, hy⟩ := Subtype.ext (by
    show (x : G) * l * (x : G)⁻¹ * (l : G)⁻¹ = (x : G) * ((l : G) * (x : G)⁻¹ * (l : G)⁻¹)
    group)
  rw [h1, vec_mul]
  congr 1
  have h2 := natLam_spec h.L_le h.Lact l x⁻¹ ⟨_, hy⟩ rfl
  rw [h2, vec_inv]

include h he in
theorem pCoreOf_Kv_le_centralizer : pCoreOf 2 (Kv hyp e) ≤ centralizer (V : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Kv hyp e with hKdef
  have hKL : K ≤ L := Kv_le_L hyp e
  set P := pCoreOf 2 K with hPdef
  have hPK : P ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKP : K ≤ normalizer (P : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  set lam := natLam h.L_le h.Lact with hlam
  set I : Subgroup (alternatingGroup (Fin 7)) := (P.subgroupOf L).map lam with hI
  have hIA : I ≤ altFive := by
    rw [← natLam_map_Kv hyp h he]
    exact map_mono fun x hx => hPK hx
  have hI2 : IsPGroup 2 I := (hP2.comap_of_injective _ L.subtype_injective).map lam
  have hIn : (I.subgroupOf altFive).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [mem_subgroupOf] at ha ⊢
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he g.2
    obtain ⟨p, hp, hpa⟩ := ha
    refine ⟨k * p * k⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf] at hp ⊢
      exact (mem_normalizer_iff.1 (hKP hkK) _).1 hp
    · rw [map_mul, map_mul, map_inv, hk, hpa]
      rfl
  have hs := isSimpleGroup_altFive
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hIn with h1 | h1
  ·
    intro x hx
    have hxL : x ∈ L := hKL (hPK hx)
    have h2 : lam ⟨x, hxL⟩ ∈ I := ⟨⟨x, hxL⟩, by rwa [SetLike.mem_coe, mem_subgroupOf], rfl⟩
    have h3 : (⟨lam ⟨x, hxL⟩, hIA h2⟩ : altFive) ∈ I.subgroupOf altFive := by
      rw [mem_subgroupOf]
      exact h2
    rw [h1, mem_bot] at h3
    have h4 : lam ⟨x, hxL⟩ = 1 := congrArg Subtype.val h3
    exact (natLam_eq_one_iff h.L_le h.Lact ⟨x, hxL⟩).1 h4
  · exfalso
    have h2 : IsPGroup 2 (I.subgroupOf altFive) :=
      hI2.comap_of_injective _ altFive.subtype_injective
    rw [h1] at h2
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
    rw [Subgroup.card_top, nat_card_altFive] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

include h he in
theorem Kv_quasisimple :
    CFSG.IsQuasisimple (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) ∧
      Nonempty ((↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) ⧸
        center (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) ≃* alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Kv hyp e with hKdef
  have hKL : K ≤ L := Kv_le_L hyp e
  set lam := natLam h.L_le h.Lact with hlam
  set θ₀ : ↥K →* alternatingGroup (Fin 7) := lam.comp (Subgroup.inclusion hKL) with hθ₀def
  have hθ₀ : ∀ k : K, θ₀ k ∈ altFive := fun k => by
    rw [← natLam_map_Kv hyp h he]
    exact ⟨Subgroup.inclusion hKL k, by rw [SetLike.mem_coe, mem_subgroupOf]; exact k.2, rfl⟩
  set θ : ↥K →* ↥altFive := θ₀.codRestrict altFive hθ₀ with hθdef
  have hθs : Function.Surjective θ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he hσ
    refine ⟨⟨k, hkK⟩, Subtype.ext ?_⟩
    show lam (Subgroup.inclusion hKL ⟨k, hkK⟩) = σ
    rw [← hk]
    rfl
  have hθ1 : ∀ k : K, θ k = 1 ↔ (k : G) ∈ centralizer (V : Set G) := fun k => by
    have := natLam_eq_one_iff h.L_le h.Lact (Subgroup.inclusion hKL k)
    constructor
    · intro h1
      exact this.1 (congrArg Subtype.val h1)
    · intro h1
      exact Subtype.ext (this.2 h1)
  have hO2 : CFSG.pCore 2 ↥K ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hθ1]
    apply pCoreOf_Kv_le_centralizer hyp h he
    rw [pCoreOf_eq_map_cfsgPCore]
    exact ⟨x, hx, rfl⟩
  set θ' : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥altFive := QuotientGroup.lift _ θ hO2 with hθ'def
  have hθ's : Function.Surjective θ' :=
    QuotientGroup.lift_surjective_of_surjective _ _ hθs hO2
  have hcen : θ'.ker ≤ center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx1 : θ x = 1 := hq
    have hxV := (hθ1 x).1 hx1
    rw [mem_center_iff]
    intro r
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
    have hc := commutator_mem_pCoreOf_of_centralizer h hyp.quasisimple (hKL x.2) hxV (hKL y.2)
    have hKN : K ≤ normalizer (pCoreOf 2 L ⊓ K : Set G) := by
      intro k hk
      have hkL := hKL hk
      exact A4.mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hkL)
        (le_normalizer hk)
    have hcK : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hKN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
        ⟨hc, K.mul_mem (K.mul_mem (K.mul_mem x.2 y.2) (K.inv_mem x.2)) (K.inv_mem y.2)⟩
    rw [pCoreOf_eq_map_cfsgPCore] at hcK
    obtain ⟨z, hz, hzeq⟩ := hcK
    have hz' : z = x * y * x⁻¹ * y⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hzeq)
    rw [hz'] at hz
    have h1 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hz
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (QuotientGroup.mk y : ↥K ⧸ CFSG.pCore 2 ↥K) * QuotientGroup.mk x
        = ((QuotientGroup.mk x * QuotientGroup.mk y * (QuotientGroup.mk x)⁻¹ *
            (QuotientGroup.mk y)⁻¹)⁻¹ * (QuotientGroup.mk x * QuotientGroup.mk y)) := by group
      _ = QuotientGroup.mk x * QuotientGroup.mk y := by rw [h1, inv_one, one_mul]
  have hKperf : Group.IsPerfect ↥K := (Subgroup.isPerfect_iff).2 (Kv_perfect hyp e)
  have hperf : Group.IsPerfect (↥K ⧸ CFSG.pCore 2 ↥K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  have hA5q : CFSG.IsQuasisimple ↥altFive := by
    have := isSimpleGroup_altFive
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup altFive_nonabelian).1
  have hq := (CFSG.LocalCores.isQuasisimple_iff_of_surjective hperf θ' hθ's hcen).2 hA5q
  have hZ : center (↥K ⧸ CFSG.pCore 2 ↥K) = θ'.ker := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hperf θ' hθ's hcen, center_altFive]
    rfl
  exact ⟨hq, ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientKerEquivOfSurjective θ' hθ's)).trans altFiveEquiv.symm⟩⟩

include h he in
theorem Kv_mem_lFamily (hTK : T ≤ normalizer (Kv hyp e : Set G)) : Kv hyp e ∈ lFamily T := by
  show Kv hyp e ∈ cComp (Kv hyp e ⊔ T)
  obtain ⟨hq, -⟩ := Kv_quasisimple hyp h he
  refine mem_cComp_of_quasisimple_quotient
    (fun N _ hN => eq_top_of_perfect_of_isPGroup (Kv_perfect hyp e) N hN) hq
    (A3.subnormal_of_normal le_sup_left ?_)
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hTK)

omit [Finite G] in
theorem pCoreOf_ne_bot_of_le_centralizer {X : Subgroup G} {x : G} (hx2 : orderOf x = 2)
    (hxX : x ∈ X) (hXx : X ≤ centralizer ({x} : Set G)) : pCoreOf 2 X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h1 => by simp [h1] at hx2
  have hle : zpowers x ≤ pCoreOf 2 X := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (zpowers_le.2 hxX) ?_
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx2, pow_one]))
    rw [normalizer_zpowers_eq_centralizer' hx2]
    exact hXx
  intro hbot
  apply hx1
  have := hle (mem_zpowers x)
  rw [hbot, mem_bot] at this
  exact this

include he in
omit [Finite G] in
theorem orderOf_eq_two_of_vecFS : orderOf (e : G) = 2 := by
  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, vec_one] at he
    exact absurd he (by decide)
  refine orderOf_eq_prime ?_ he1
  rw [pow_two]
  exact congrArg Subtype.val (sq_eq_one_of_vec ψ e)

include h he in
theorem Kv_isLocal (hTK : T ≤ normalizer (Kv hyp e : Set G))
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) : quasithinIsLocal T (Kv hyp e) := by
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ centralizer ({(e : G)} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC heZ) t ht))
  refine ⟨hyp.sylow.1, Kv_mem_lFamily hyp h he hTK,
    (isSylowTwoOf_of_le hyp.sylow le_sup_right).2.2, ?_⟩
  exact pCoreOf_ne_bot_of_le_centralizer (orderOf_eq_two_of_vecFS he)
    ((le_sup_right : T ≤ Kv hyp e ⊔ T) (h.le_T e.2)) (sup_le (Kv_le_centralizer hyp e) hTe)

@[expose] def vecZS : Fin 7 → ZMod 2 := fun i => if i = 0 ∨ i = 6 then 1 else 0

@[expose] def vecZT : Fin 7 → ZMod 2 := fun i => if i = 0 ∨ i = 2 then 1 else 0

@[expose] def vecQuad : Fin 7 → ZMod 2 := fun i => if (i : ℕ) < 4 then 1 else 0

theorem vecZS_mem : vecZS ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide

theorem vecZT_mem : vecZT ∈ evenWeight 7 := by
  rw [mem_evenWeight]
  decide

theorem hammingNorm_vecFS_add_vecQuad : hammingNorm (vecFS + vecQuad) = 6 := by
  decide

@[expose] def a5cyc234 : alternatingGroup (Fin 7) :=
  ⟨swap 2 3 * swap 3 4, by rw [mem_alternatingGroup]; decide⟩

theorem a5cyc234_mem : a5cyc234 ∈ altFive := by
  rw [mem_altFive]
  decide

theorem not_fixed_of_weight_four : ∀ w : Fin 7 → ZMod 2, hammingNorm w = 4 →
    permAct7 (a5cyc012 : Perm (Fin 7)) w ≠ w ∨ permAct7 (a5cyc234 : Perm (Fin 7)) w ≠ w := by
  decide +kernel

include h he in
theorem exists_weight_four_mem_commutator :
    ∃ v : V, (v : G) ∈ ⁅V, Kv hyp e⁆ ∧ vec ψ v = vecQuad := by
  obtain ⟨u, hu⟩ := exists_vec_eq ψ vecZT_mem
  obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he a5dbl0123_mem
  obtain ⟨hc, hvec⟩ := vec_commutator_natLam h u k
  refine ⟨⟨_, hc⟩, commutator_mem_commutator u.2 hkK, ?_⟩
  rw [hvec, hu, hk]
  decide

include h he in
theorem exists_commutator_ne_one_of_weight_four {y : V} (hy : hammingNorm (vec ψ y) = 4) :
    ∃ k ∈ Kv hyp e, (y : G) * k * (y : G)⁻¹ * k⁻¹ ≠ 1 := by
  have key : ∀ σ : alternatingGroup (Fin 7), σ ∈ altFive →
      permAct7 (σ : Perm (Fin 7)) (vec ψ y) ≠ vec ψ y →
      ∃ k ∈ Kv hyp e, (y : G) * k * (y : G)⁻¹ * k⁻¹ ≠ 1 := by
    intro σ hσ hne
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he hσ
    obtain ⟨hc, hvec⟩ := vec_commutator_natLam h y k
    refine ⟨k, hkK, fun h1 => hne ?_⟩
    have h2 : (⟨_, hc⟩ : V) = 1 := Subtype.ext h1
    rw [h2, vec_one, hk] at hvec
    have h3 := congrArg (· + permAct7 (σ : Perm (Fin 7)) (vec ψ y)) hvec
    simp only [zero_add] at h3
    rw [add_assoc, fun_add_self_eq_zero, add_zero] at h3
    exact h3
  rcases not_fixed_of_weight_four _ hy with h1 | h1
  · exact key _ a5cyc012_mem h1
  · exact key _ a5cyc234_mem h1

include h he in
theorem VY_Kv_ne_bot (hTK : T ≤ normalizer (Kv hyp e : Set G)) : VY (Kv hyp e) ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Kv hyp e with hKdef
  have hKL : K ≤ L := Kv_le_L hyp e
  have hVK : V ≤ normalizer (K : Set G) := (h.le_T).trans hTK
  have hKV : K ≤ normalizer (V : Set G) := hKL.trans h.L_le
  set W := ⁅V, K⁆ with hWdef
  have hWK : W ≤ K := (Subgroup.le_normalizer_iff_commutator_le_right).1 hVK
  have hWV : W ≤ V := (Subgroup.le_normalizer_iff_commutator_le_left).1 hKV
  have hV2 : IsPGroup 2 V := fun x => ⟨1, by
    rw [pow_one, pow_two]
    exact sq_eq_one_of_vec ψ x⟩
  have hVKp : V ⊓ K ≤ pCoreOf 2 K := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      (hV2.to_le inf_le_left)
    intro k hk
    exact A4.mem_normalizer_inf (hKV hk) (le_normalizer hk)
  have hPV := pCoreOf_Kv_le_centralizer hyp h he
  have hWZ : W ≤ omegaOneCenterOf (pCoreOf 2 K) := by
    intro w hw
    refine Subgroup.subset_closure ⟨⟨hVKp ⟨hWV hw, hWK hw⟩, ?_⟩, ?_⟩
    · exact (Subgroup.le_centralizer_iff.1 hPV) (hWV hw)
    · rw [pow_two]
      exact congrArg Subtype.val (sq_eq_one_of_vec ψ ⟨w, hWV hw⟩)
  obtain ⟨u, hu⟩ := exists_vec_eq ψ vecZS_mem
  obtain ⟨k₁, hk₁K, hk₁⟩ := exists_mem_Kv_natLam hyp h he a5cyc012_mem
  obtain ⟨hc₁, hvec₁⟩ := vec_commutator_natLam h u k₁
  set w : V := ⟨_, hc₁⟩ with hwdef
  have hwW : (w : G) ∈ W := commutator_mem_commutator u.2 hk₁K
  obtain ⟨k₂, hk₂K, hk₂⟩ := exists_mem_Kv_natLam hyp h he a5cyc123_mem
  obtain ⟨hc₂, hvec₂⟩ := vec_commutator_natLam h w k₂
  have hne : (⟨_, hc₂⟩ : V) ≠ 1 := by
    intro h1
    rw [h1, vec_one, hk₂, hvec₁, hu, hk₁] at hvec₂
    exact absurd hvec₂ (by decide)
  intro hbot
  apply hne
  apply Subtype.ext
  have hmem : (w : G) * k₂ * (w : G)⁻¹ * (k₂ : G)⁻¹ ∈ VY K :=
    Subgroup.commutator_mono hWZ le_rfl (commutator_mem_commutator hwW hk₂K)
  rw [hbot, mem_bot] at hmem
  exact hmem

include h he in
theorem Kv_isFaithfulLocal (hTK : T ≤ normalizer (Kv hyp e : Set G))
    (heZ : (e : G) ∈ quasithinOmegaOneCenter T) : quasithinIsFaithfulLocal T (Kv hyp e) := by
  have hloc := Kv_isLocal hyp h he hTK heZ
  exact isFaithfulLocal_iff_isXf.2 ⟨hloc, isXClass_of_isLocal hyp.qtke hyp.sylow hloc,
    VY_Kv_ne_bot hyp h he hTK⟩

end Ke

end CFSG.Quasithin.H13.A7
