module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316U35B
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316KGU35
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Rank
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316U35A

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem exists_lift (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {k₁ : G}
    (hk₁ : k₁ ∈ KZ) (ho : orderOf k₁ = 5) {a b : ↥s.rho.range} (ha : a ∈ s.star KZ)
    (hb : b ∈ s.star KZ) (hx : s.rho.rangeRestrict ⟨k₁, s.KZ_le_G₀ hk₁⟩ = a * b * a⁻¹ * b⁻¹)
    (hab : ∀ g ∈ Subgroup.closure ({a, b} : Set ↥s.rho.range), g ^ 5 = 1 ∧
      g * s.rho.rangeRestrict ⟨k₁, s.KZ_le_G₀ hk₁⟩ = s.rho.rangeRestrict ⟨k₁, s.KZ_le_G₀ hk₁⟩ * g) :
    ∃ a' ∈ KZ, ∃ b' ∈ KZ, k₁ = a' * b' * a'⁻¹ * b'⁻¹ ∧
      ∀ g ∈ Subgroup.closure ({a', b'} : Set G), g ^ 5 = 1 ∧ g * k₁ = k₁ * g := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set φ : ↥KZ →* ↥s.rho.range := s.rho.rangeRestrict.comp (Subgroup.inclusion s.KZ_le_G₀)
    with hφ
  have hφrange : φ.range = s.star KZ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hφker : φ.ker = (s.starHom s.KZ_le_G₀).ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hcop : Nat.Coprime 5 (Nat.card φ.ker) := by
    rw [hφker]
    exact s.coprime_card_ker_starHom h135 hR hC h36 h37 h38 h39
  set A := Subgroup.closure ({a, b} : Set ↥s.rho.range) with hA
  have haA : a ∈ A := Subgroup.subset_closure (Set.mem_insert a {b})
  have hbA : b ∈ A := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hAle : A ≤ φ.range := by
    rw [hφrange, hA, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ha
    · exact hb
  have hA5 : IsPGroup 5 ↥(⊤ : Subgroup ↥A) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, SubgroupClass.coe_pow]
      exact (hab _ (g : ↥A).2).1))⟩
  set H₀ := A.comap φ with hH₀
  set k₁' : ↥KZ := ⟨k₁, hk₁⟩ with hk₁'
  have hk₁H : k₁' ∈ H₀ := by
    show φ k₁' ∈ A
    rw [show φ k₁' = s.rho.rangeRestrict ⟨k₁, s.KZ_le_G₀ hk₁⟩ from rfl, hx]
    exact A.mul_mem (A.mul_mem (A.mul_mem haA hbA) (A.inv_mem haA)) (A.inv_mem hbA)
  set k₁'' : ↥H₀ := ⟨k₁', hk₁H⟩ with hk₁''
  have hk₁o : orderOf k₁'' = 5 := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ho]
  have hZ5 : IsPGroup 5 ↥(Subgroup.zpowers k₁'') := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hk₁o]
    exact ⟨1, by norm_num⟩
  obtain ⟨P, hP⟩ := hZ5.exists_le_sylow
  have hk₁P : k₁'' ∈ (P : Subgroup ↥H₀) := hP (Subgroup.mem_zpowers _)
  let ψ : ↥H₀ →* ↥A := φ.subgroupComap A
  have hψv : ∀ h : ↥H₀, ((ψ h : ↥A) : ↥s.rho.range) = φ h := fun _ => rfl
  have hψ : Function.Surjective ψ := by
    rintro ⟨x, hx'⟩
    obtain ⟨k, hk⟩ := hAle hx'
    exact ⟨⟨k, show φ k ∈ A from hk ▸ hx'⟩, Subtype.ext hk⟩
  have hPA : (P : Subgroup ↥H₀).map ψ = ⊤ := by
    have h := (P.mapSurjective hψ).is_maximal' hA5 le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have hinj : ∀ p ∈ (P : Subgroup ↥H₀), ψ p = 1 → p = 1 := by
    intro p hp h1
    have hpker : (p : ↥KZ) ∈ φ.ker := by
      rw [MonoidHom.mem_ker, ← hψv, h1]
      rfl
    obtain ⟨e, he⟩ := P.isPGroup' ⟨p, hp⟩
    have h2 : orderOf p ∣ 5 ^ e := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val he)
    have h3 : orderOf p ∣ Nat.card φ.ker := by
      have := orderOf_dvd_natCard (⟨(p : ↥KZ), hpker⟩ : ↥φ.ker)
      rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at this
    have h4 : orderOf p = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left e hcop) h2 h3
    exact orderOf_eq_one_iff.mp h4
  have hinj' : ∀ p ∈ (P : Subgroup ↥H₀), ∀ q ∈ (P : Subgroup ↥H₀), ψ p = ψ q → p = q := by
    intro p hp q hq h
    have := hinj (p⁻¹ * q) ((P : Subgroup ↥H₀).mul_mem ((P : Subgroup ↥H₀).inv_mem hp) hq)
      (by rw [map_mul, map_inv, h, inv_mul_cancel])
    exact inv_mul_eq_one.mp this
  obtain ⟨a₁, ha₁P, ha₁⟩ := (show (⟨a, haA⟩ : ↥A) ∈ (P : Subgroup ↥H₀).map ψ from
    hPA ▸ Subgroup.mem_top _)
  obtain ⟨b₁, hb₁P, hb₁⟩ := (show (⟨b, hbA⟩ : ↥A) ∈ (P : Subgroup ↥H₀).map ψ from
    hPA ▸ Subgroup.mem_top _)
  have hcommP : a₁ * b₁ * a₁⁻¹ * b₁⁻¹ ∈ (P : Subgroup ↥H₀) :=
    (P : Subgroup ↥H₀).mul_mem ((P : Subgroup ↥H₀).mul_mem ((P : Subgroup ↥H₀).mul_mem ha₁P hb₁P)
      ((P : Subgroup ↥H₀).inv_mem ha₁P)) ((P : Subgroup ↥H₀).inv_mem hb₁P)
  have hψk : ψ k₁'' = ⟨a * b * a⁻¹ * b⁻¹, A.mul_mem (A.mul_mem (A.mul_mem haA hbA)
      (A.inv_mem haA)) (A.inv_mem hbA)⟩ := Subtype.ext (by rw [hψv]; exact hx)
  have hcomm : a₁ * b₁ * a₁⁻¹ * b₁⁻¹ = k₁'' := by
    apply hinj' _ hcommP _ hk₁P
    rw [hψk, map_mul, map_mul, map_mul, map_inv, map_inv, ha₁, hb₁]
    rfl
  set PG : Subgroup G := ((P : Subgroup ↥H₀).map H₀.subtype).map KZ.subtype with hPG
  have hmemPG : ∀ g ∈ PG, ∃ p ∈ (P : Subgroup ↥H₀), ((p : ↥KZ) : G) = g := by
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, rfl⟩
  refine ⟨((a₁ : ↥KZ) : G), (a₁ : ↥KZ).2, ((b₁ : ↥KZ) : G), (b₁ : ↥KZ).2, ?_, fun g hg => ?_⟩
  · have := congrArg (fun h : ↥H₀ => ((h : ↥KZ) : G)) hcomm
    simpa using this.symm
  · have hcl : Subgroup.closure ({((a₁ : ↥KZ) : G), ((b₁ : ↥KZ) : G)} : Set G) ≤ PG := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨_, ⟨a₁, ha₁P, rfl⟩, rfl⟩
      · exact ⟨_, ⟨b₁, hb₁P, rfl⟩, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hmemPG g (hcl hg)
    have hψpA := hab _ (ψ p).2
    constructor
    · have h1 : p ^ 5 = 1 := by
        apply hinj _ ((P : Subgroup ↥H₀).pow_mem hp 5)
        apply Subtype.ext
        rw [map_pow, SubgroupClass.coe_pow, hψpA.1]
        rfl
      have := congrArg (fun h : ↥H₀ => ((h : ↥KZ) : G)) h1
      simpa using this
    · have h1 : p * k₁'' = k₁'' * p := by
        apply hinj' _ ((P : Subgroup ↥H₀).mul_mem hp hk₁P) _
          ((P : Subgroup ↥H₀).mul_mem hk₁P hp)
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
        have hk : ((ψ k₁'' : ↥A) : ↥s.rho.range) = s.rho.rangeRestrict ⟨k₁, s.KZ_le_G₀ hk₁⟩ := rfl
        rw [hk]
        exact hψpA.2
      have := congrArg (fun h : ↥H₀ => ((h : ↥KZ) : G)) h1
      simpa using this

theorem charTwo_KZ : CharTwo KZ := by
  have hGZ : CharTwo (Subgroup.normalizer (ZS : Set G)) :=
    charTwo_of_inH s.sk.base.hyp.qtke.2.1 (s.sk.base.hyp.sylow.1.toSylow s.sk.base.hyp.sylow.2)
      s.inH_GZ
  have hKZGZ : KZ ≤ Subgroup.normalizer (ZS : Set G) := le_of_mem_cComp s.KZ_mem
  have hn : (KZ.subgroupOf (Subgroup.normalizer (ZS : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).mpr s.KZ_normal
  exact CharTwo.of_isSubnormal hGZ hKZGZ hn.isSubnormal

end Setting4315

theorem step43U35_of (hKG : KGU35) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Step43U35 := by
  intro G _ _ T M L n I H K t m F _ _ α β W' ZS K₂ R₂ μ y KZ s hm hU
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  have hF4 : Fintype.card F = 4 := by rw [s.card_F, hm]; norm_num
  have hS : IsPSU 3 5 1 ↥(s.star KZ) :=
    IsPSU.of_mulEquiv (s.mulEquiv_star_KZ.trans (L4315.innEquiv _).symm).symm hU
  have := s.star_KZ_normal
  rcases hKG ↥s.rho.range (s.star KZ) s.star_KZ_normal hS (s.centralizer_star_KZ hq) F hF4
    (s.star R₂) (s.star K₂) (s.star_R₂_ne_bot h135 hR hC h36 h37 h38 h39) s.isPGroup_star_R₂
    s.star_K₂_le s.star_K₂_perfect s.star_K₂_le_normalizer
    (s.normalizer_star_R₂_le h135 hR hC h37 h38 h39) s.exists_chi with ⟨hinf, hcard⟩ | h5
  · exact s.false_of_star_R₂_inf_eq_bot h135 hR hC h36 h37 h38 h39 hinf hcard
  obtain ⟨k₁, hk₁, ho, hkK, hrow⟩ := s.exists_k₁ h135 hR hC h37 h38 h39 hm
  have hk₁Z : k₁ ∈ KZ := s.K₂_le_KZ hk₁
  set x := s.rho.rangeRestrict ⟨k₁, s.K₂_le_G₀ hk₁⟩ with hxdef
  have hxK : x ∈ s.star K₂ := ⟨⟨k₁, s.K₂_le_G₀ hk₁⟩, hk₁, rfl⟩
  have hx1 : x ≠ 1 := by
    intro h
    have hker : (⟨k₁, hk₁Z⟩ : ↥KZ) ∈ (s.starHom s.KZ_le_G₀).ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h
    have h1 := orderOf_dvd_natCard (⟨⟨k₁, hk₁Z⟩, hker⟩ : ↥(s.starHom s.KZ_le_G₀).ker)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ho] at h1
    have h2 := s.coprime_card_ker_starHom h135 hR hC h36 h37 h38 h39
    exact absurd (Nat.Coprime.eq_one_of_dvd h2 h1) (by norm_num)
  have hxo : orderOf x = 5 := by
    refine orderOf_eq_prime ?_ hx1
    rw [hxdef, ← map_pow]
    have : (⟨k₁, s.K₂_le_G₀ hk₁⟩ : ↥s.G₀) ^ 5 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← ho]
      exact pow_orderOf_eq_one k₁
    rw [this, map_one]
  obtain ⟨a, ha, b, hb, hxab, hab⟩ := h5 x hxK hxo
  obtain ⟨a', ha', b', hb', hk₁ab, hab'⟩ := s.exists_lift h135 hR hC h36 h37 h38 h39 hk₁Z ho ha hb
    hxab (fun g hg => ⟨(hab g hg).1, (hab g hg).2⟩)
  set T₀ := pCoreOf 2 KZ with hT₀
  have hQT : Subgroup.closure ({a', b'} : Set G) ≤ Subgroup.normalizer (T₀ : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact le_normalizer_pCoreOf 2 KZ ha'
    · exact le_normalizer_pCoreOf 2 KZ hb'
  have haQ : a' ∈ Subgroup.closure ({a', b'} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbQ : b' ∈ Subgroup.closure ({a', b'} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hnt : ¬ T₀ ≤ Subgroup.centralizer ({a' * b' * a'⁻¹ * b'⁻¹} : Set G) := by
    rw [← hk₁ab]
    intro hle
    have hkC : k₁ ∈ Subgroup.centralizer (T₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hle ht) k₁ (Set.mem_singleton k₁)).symm
    have hkT : k₁ ∈ T₀ := s.charTwo_KZ ⟨hk₁Z, hkC⟩
    obtain ⟨e, he⟩ := (pCoreOf_isPGroup 2 KZ) ⟨k₁, hkT⟩
    have h1 : orderOf k₁ ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val he)
    rw [ho] at h1
    have h2 := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 5) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h1)
    omega
  have h20 := L4316.two_pow_twenty_mul_card_le (pCoreOf_isPGroup 2 KZ) hQT
    (fun g hg => (hab' g hg).1) haQ hbQ (by
      rw [← hk₁ab]
      intro g hg
      exact (hab' g hg).2) hnt
  rw [← hk₁ab] at h20
  have hTR : T₀ ≤ R₂ := s.pCoreOf_KZ_le
  have h16 := s.card_R₂_le h135 hR hC h37 h38 h39 hm hk₁ ho hkK hrow
  set C := Subgroup.centralizer ({k₁} : Set G) with hCdef
  have hne : C.relIndex R₂ ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_mul_card (H := C) (K := R₂)
    rw [h0, zero_mul] at this
    exact (Nat.card_pos (α := ↥R₂)).ne' this.symm
  have hrel : C.relIndex T₀ ≤ C.relIndex R₂ := Subgroup.relIndex_le_of_le_right hTR hne
  have hT₀ := Subgroup.relIndex_mul_card (H := C) (K := T₀)
  have hR₂ := Subgroup.relIndex_mul_card (H := C) (K := R₂)
  rw [inf_comm] at hT₀ hR₂
  have hpos : 0 < Nat.card ↥(T₀ ⊓ C) := Nat.card_pos
  have hpos' : 0 < Nat.card ↥(R₂ ⊓ C) := Nat.card_pos
  have h1 : 2 ^ 20 ≤ C.relIndex T₀ := by
    rw [← hT₀] at h20
    exact Nat.le_of_mul_le_mul_right h20 hpos
  have h2 : C.relIndex R₂ ≤ 2 ^ 16 := by
    rw [← hR₂] at h16
    exact Nat.le_of_mul_le_mul_right h16 hpos'
  have := h1.trans (hrel.trans h2)
  norm_num at this

end CFSG.Quasithin.H13.Ch4
