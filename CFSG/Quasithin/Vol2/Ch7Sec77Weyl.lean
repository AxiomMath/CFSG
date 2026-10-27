module

public import CFSG.Quasithin.Vol2.Ch7Sec77Hyp
public import CFSG.Quasithin.Background.HBlockWeyl
public import CFSG.Quasithin.Background.C2Seven
public import CFSG.Quasithin.Background.C24PfD
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InComplement
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_mem_normalizer_of_conj_le {A N : Subgroup G} {g : G} (hAo : Odd (Nat.card A))
    (hN2 : IsPGroup 2 N) (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ N ⊔ A) :
    ∃ z ∈ N, z * g ∈ Subgroup.normalizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := N ⊔ A with hF
  have hNF : N ≤ F := le_sup_left
  have hAF : A ≤ F := le_sup_right
  have hFN : F ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hAN
  have hNA : N ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : Odd (orderOf x) := by
      have := orderOf_dvd_natCard (⟨x, hx.2⟩ : A)
      rw [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hAo this
    exact (Subgroup.mem_bot).2 (eq_one_of_odd_of_mem hN2 hx.1 h1)
  have hA : Lin2.IsComplementIn N F A :=
    ⟨hAF, hNA, fun f hf => (Lin2.mem_sup_iff_of_le_normalizer hAN).1 hf⟩
  have hgF : g ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : F.map (MulAut.conj g).toMonoidHom ≤ F := by
      rw [hF, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨n, hn, rfl⟩
        exact hNF ((Subgroup.mem_normalizer_iff.mp hgN n).mp hn)
      · rintro _ ⟨a, ha, rfl⟩
        exact hg a ha
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hA' := hA.conj (g := g⁻¹) (Subgroup.inv_mem _ hgF) (Subgroup.inv_mem _ hgN)
  have hodd : ¬ 2 ∣ N.relIndex F := by
    have h1 := Subgroup.relIndex_mul_card (H := N) (K := F)
    rw [inf_eq_left.mpr hNF, hA.card_mul hNF hFN] at h1
    have h2 : N.relIndex F = Nat.card A :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1, mul_comm])
    rw [h2]
    exact hAo.not_two_dvd_nat
  obtain ⟨r, hr, hrA⟩ := Lin2.exists_conj_of_complements hNF hFN hN2 hodd hA.1 hA'.1 hA.2.1
    hA'.2.1 hA.2.2 hA'.2.2
  refine ⟨r, hr, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have key : ∀ y : G, y ∈ conjR A g⁻¹ ↔ y ∈ conjR A r := fun y => by rw [hrA]
  simp only [Lin2.mem_conjR, inv_inv] at key
  constructor
  · intro hx
    have h1 := (key (g * x * g⁻¹)).1 (by
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]; exact hx)
    have e : r * (g * x * g⁻¹) * r⁻¹ = r * g * x * (r * g)⁻¹ := by group
    rwa [e] at h1
  · intro hx
    have e : r * (g * x * g⁻¹) * r⁻¹ = r * g * x * (r * g)⁻¹ := by group
    have h1 := (key (g * x * g⁻¹)).2 (by rw [e]; exact hx)
    have e2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e2] at h1

theorem card_ne_three_of_isQuasisimple {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) : Nat.card X ≠ 3 := by
  intro h3
  obtain ⟨-, -, a, b, hab⟩ := hX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic X := isCyclic_of_prime_card h3
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    (IsCyclic.isMulCommutative (α := X)).is_comm.comm x y]

omit [Finite G] in
theorem card_quot_of_isAltType_three {K : Subgroup G} (h : IsAltType K 3) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
  obtain ⟨α, hαs, hαk, -⟩ := h
  rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
    Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem exists_pow_of_odd (hc : S.Coord θ e) {y : G} (hyM : y ∈ fsuM T L)
    (hy0 : y ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G))
    (hyo : Odd (orderOf y)) (hyV : y ∉ Subgroup.centralizer (fsuV T I : Set G)) :
    ∃ m : ℕ, θ * (y ^ m)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  set X := fsuM T L ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
    Subgroup G) : Set G) with hX
  have hXM : X ≤ fsuM T L := inf_le_left
  have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)))
  obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
  set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
  have hcent : ∀ x : ↥X, χ x = 1 → (x : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro x hx
    have hb : blk (φ x : SL32) = 1 := by
      have h1 : (χ x : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [hx]; rfl
      rwa [hχ, MonoidHom.comp_apply, coe_blkHom] at h1
    exact mem_centralizer_of_blk (S.hMN (hXM x.2)) (φ x).2 hb (hφ x).symm
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_b1_mem_V0 hc)) x.2.2)
  have hθX : θ ∈ X := ⟨S.L_le_fsuM hc.mem, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp hv.2⟩
  have hyX : y ∈ X := ⟨hyM, hy0⟩
  have hφθ : (φ ⟨θ, hθX⟩ : SL32) = th0 := SL3One.rho_injective ((hφ ⟨θ, hθX⟩).trans hc.hθ)
  have hφθ3 : φ ⟨θ, hθX⟩ ^ 3 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, hφθ, th0_pow_three, OneMemClass.coe_one])
  have hχθ3 : χ ⟨θ, hθX⟩ ^ 3 = 1 := by
    rw [hχ, MonoidHom.comp_apply, ← map_pow, hφθ3, map_one]
  have hχθ1 : χ ⟨θ, hθX⟩ ≠ 1 := by
    intro h
    have h1 : (χ ⟨θ, hθX⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [h]; rfl
    rw [hχ, MonoidHom.comp_apply, coe_blkHom, hφθ] at h1
    exact blk_th0_ne_one h1
  have hχy3 : χ ⟨y, hyX⟩ ^ 3 = 1 := by
    have h1 : χ ⟨y, hyX⟩ ^ orderOf y = 1 := by
      rw [← map_pow]
      have : (⟨y, hyX⟩ : ↥X) ^ orderOf y = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
      rw [this, map_one]
    have h2 : χ ⟨y, hyX⟩ ^ Nat.gcd (orderOf y) 6 = 1 :=
      pow_gcd_eq_one.mpr ⟨h1, gl2_pow_six (χ ⟨y, hyX⟩)⟩
    have h3 : Nat.gcd (orderOf y) 6 ∣ 3 := by
      have h4 : Nat.Coprime (orderOf y) 2 := Nat.coprime_two_right.mpr hyo
      have h5 : Nat.gcd (orderOf y) 6 ∣ Nat.gcd (orderOf y) 2 * Nat.gcd (orderOf y) 3 :=
        (Nat.Coprime.gcd_mul (orderOf y) (by norm_num : Nat.Coprime 2 3)).dvd
      rw [h4.gcd_eq_one, one_mul] at h5
      exact h5.trans (Nat.gcd_dvd_right _ _)
    obtain ⟨c, hc'⟩ := h3
    rw [hc', pow_mul, h2, one_pow]
  have hθy : ∀ m : ℕ, χ ⟨θ, hθX⟩ * (χ ⟨y, hyX⟩ ^ m)⁻¹ = 1 →
      θ * (y ^ m)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro m hm
    have hmem : θ * (y ^ m)⁻¹ ∈ X := X.mul_mem hθX (X.inv_mem (X.pow_mem hyX m))
    refine hcent ⟨_, hmem⟩ ?_
    have e : (⟨θ * (y ^ m)⁻¹, hmem⟩ : ↥X) = ⟨θ, hθX⟩ * ((⟨y, hyX⟩ : ↥X) ^ m)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_pow]
    exact hm
  rcases gl2_cube_cases _ _ hχθ3 hχθ1 hχy3 with h | h | h
  · exact absurd (hcent ⟨y, hyX⟩ h) hyV
  · exact ⟨1, hθy 1 (by rw [pow_one, h, mul_inv_cancel])⟩
  · refine ⟨2, hθy 2 ?_⟩
    have h4 : (χ ⟨θ, hθX⟩ * χ ⟨θ, hθX⟩) ^ 2 = χ ⟨θ, hθX⟩ := by
      calc (χ ⟨θ, hθX⟩ * χ ⟨θ, hθX⟩) ^ 2 = χ ⟨θ, hθX⟩ ^ 3 * χ ⟨θ, hθX⟩ := by
            rw [← pow_two, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ]
        _ = χ ⟨θ, hθX⟩ := by rw [hχθ3, one_mul]
    rw [h, h4, mul_inv_cancel]

theorem vm_le_commutator (hc : S.Coord θ e) {y : G} {m : ℕ}
    (hm : θ * (y ^ m)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G))
    (hyN : y ∈ Subgroup.normalizer (fsuV T I : Set G)) :
    S.vm e ≤ ⁅S.vm e, Subgroup.zpowers y⁆ := by
  intro w hw
  obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
  obtain ⟨q, hq, rfl⟩ := exists_pairVm hp
  have hqV : S.vec e q ∈ fsuV T I := vec_mem q
  have hinv : (S.vec e q)⁻¹ = S.vec e q := vec_inv_eq q
  have hymv : y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hyN m) _).mp ((fsuV T I).inv_mem hqV)
  have hθq : θ * (S.vec e q)⁻¹ * θ⁻¹ = y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹ := by
    have h1 := Subgroup.mem_centralizer_iff.mp hm _ hymv
    calc θ * (S.vec e q)⁻¹ * θ⁻¹
        = (θ * (y ^ m)⁻¹) * (y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹)⁻¹ := by
          group
      _ = (y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹)⁻¹ := by
          rw [h1]
      _ = y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹ := by group
  have h : S.vec e (q * SL3One.rho th0 q) = ⁅S.vec e q, y ^ m⁆ := by
    calc S.vec e (q * SL3One.rho th0 q) = S.vec e q * (θ * S.vec e q * θ⁻¹) := by
          rw [vec_mul, conj_vec_th hc]
      _ = S.vec e q * (θ * (S.vec e q)⁻¹ * θ⁻¹) := by rw [hinv]
      _ = S.vec e q * (y ^ m * (S.vec e q)⁻¹ * (y ^ m)⁻¹) := by rw [hθq]
      _ = ⁅S.vec e q, y ^ m⁆ := by rw [commutatorElement_def]; group
  rw [h]
  exact Subgroup.commutator_mem_commutator (vec_mem_vm hq)
    (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) m)

theorem eq_one_of_mem_vm (hc : S.Coord θ e) {y : G} {m : ℕ}
    (hm : θ * (y ^ m)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G)) {v : G} (hv : v ∈ S.vm e)
    (hyv : y * v = v * y) : v = 1 := by
  have hvV : v ∈ fsuV T I := vm_le hv
  have hymv : y ^ m * v * (y ^ m)⁻¹ = v := by
    have : Commute y v := hyv
    rw [(this.pow_left m).eq, mul_inv_cancel_right]
  have hθv : θ * v * θ⁻¹ = v := by
    have hymvV : y ^ m * v * (y ^ m)⁻¹ ∈ fsuV T I := by rw [hymv]; exact hvV
    have h1 := Subgroup.mem_centralizer_iff.mp hm _ hymvV
    calc θ * v * θ⁻¹
        = (θ * (y ^ m)⁻¹) * (y ^ m * v * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹)⁻¹ := by group
      _ = (y ^ m * v * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹) * (θ * (y ^ m)⁻¹)⁻¹ := by rw [h1]
      _ = v := by rw [hymv]; group
  obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hv
  rw [conj_vec_th hc] at hθv
  have hp1 : SL3One.rho th0 p = p := vec_injective hθv
  have hv1 := congrArg vp hp1
  rw [vp_rho, dact_th0] at hv1
  have hx : act th0 (vp p).1 = (vp p).1 := congrArg Prod.fst hv1
  have hy : th0d *ᵥ (vp p).2 = (vp p).2 := congrArg Prod.snd hv1
  have hp' : InVm (vp p) := mem_pairVm.mp hp
  rcases (fix_th0 _).mp hx with h1 | h1
  · rcases (dfix_th0 _).mp hy with h2 | h2
    · have h3 : vp p = vp 1 := Prod.ext h1 h2
      rw [vp_injective h3]
      exact vec_one
    · exfalso
      have := hp'.2
      rw [h2] at this
      exact absurd this (by decide)
  · exfalso
    have := hp'.1
    rw [h1] at this
    exact absurd this (by decide)

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem pCoreOf_le_fsuM {K : Subgroup G} (hK : K ∈ cComp H) : pCoreOf 2 K ≤ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
    (C.conf.sylH.pCoreOf_le.trans (inf_le_left.trans S.T_le_fsuM))

theorem false_of_block (h443 : Stmt4_4_3Orbit') (hF : CharTwo H) {K P : Subgroup G}
    (hK : K ∈ cComp H) (htype : (∃ n, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 5)
    (hP : IsSylowTwoOf P K) (hB1 : K ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G))
    (hB2 : K ⊓ Subgroup.normalizer (P : Set G) ≤ fsuM T L)
    (hQK : ¬ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K ≤ pCoreOf 2 K) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨y, w, hW, hsmall, hfaith⟩ : ∃ y w : G, WeylData K P y w ∧
      (orderOf y ≤ 3 → Nat.card (blockU K) = 16 * Nat.card (blockZ K)) ∧
      (∀ s ∈ K, (∀ u ∈ blockU K, s * u * s⁻¹ * u⁻¹ ∈ blockZ K) → s ∈ pCoreOf 2 K) := by
    rcases htype with ⟨n, hn, hlin⟩ | h5
    · obtain ⟨y, w, hW, hle⟩ := exists_weylData_lin2 hn hlin hP
      refine ⟨y, w, hW, fun h3 => ?_, fun s hs hcs => mem_pCoreOf_of_comm_lin2 hlin hs hcs⟩
      have hn2 : n = 2 := by
        by_contra hcon
        have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hn2
      rw [card_blockU_lin2 hlin]
      norm_num
    · obtain ⟨y, w, hW, -⟩ := exists_weylData_alt5 h5 hP
      exact ⟨y, w, hW, fun _ => card_blockU_alt5 h5,
        fun s hs hcs => mem_pCoreOf_of_comm_alt5 h5 hs hcs⟩
  have hO2M : pCoreOf 2 K ≤ fsuM T L := C.pCoreOf_le_fsuM hK
  have hyM : y ∈ fsuM T L := hB2 ⟨hW.y_mem, hW.y_norm⟩
  have hy0 : y ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G) := by
    have := C.conf.hHG (hKH hW.y_mem)
    rwa [C.hVp] at this
  have hyN : y ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN hyM
  set Y := Subgroup.zpowers y with hY
  have hYM : Y ≤ fsuM T L := (Subgroup.zpowers_le).mpr hyM
  have hYK : Y ≤ K := (Subgroup.zpowers_le).mpr hW.y_mem
  have hYo : Odd (Nat.card Y) := by rw [hY, Nat.card_zpowers]; exact hW.y_odd
  have hYz : Y ≤ Subgroup.centralizer ({S.vec e a1} : Set G) := by
    refine (Subgroup.zpowers_le).mpr ?_
    exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)) hy0
  have hidx := S.relIndex_le_three hYM hYo (vec_mem a1) vec_a1_ne_one hYz
  by_cases hA : Y ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥
  ·
    have hy3 : orderOf y ≤ 3 := by
      rw [hA, Subgroup.relIndex_bot_left, hY, Nat.card_zpowers] at hidx
      exact hidx
    have hcard := hsmall hy3
    have hyV : y ∉ Subgroup.centralizer (fsuV T I : Set G) := by
      intro h
      have hy1 : y ∈ Y ⊓ Subgroup.centralizer (fsuV T I : Set G) := ⟨Subgroup.mem_zpowers y, h⟩
      rw [hA, Subgroup.mem_bot] at hy1
      have := hW.y_three
      rw [hy1, orderOf_one] at this
      omega
    obtain ⟨m, hm⟩ := exists_pow_of_odd hc hyM hy0 hW.y_odd hyV
    obtain ⟨-, hred⟩ := C.isTwoReduced_U hF
    have hVO : fsuV T I ≤ pCoreOf 2 H :=
      C.V_le_U.trans (CFSG.Quasithin.A4.le_pCoreOf_of_isTwoReducedIn hred)
    have hON : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
      CFSG.Quasithin.P134.pCoreOf_le_normalizer_of_mem_cComp hK
    have hOK : pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 H (hKH hk), Subgroup.le_normalizer hk⟩)
        ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    have hcomm : ⁅S.vm e, Y⁆ ≤ pCoreOf 2 K := by
      rw [Subgroup.commutator_le]
      intro v hv t ht
      have hvO : v ∈ pCoreOf 2 H := hVO (vm_le hv)
      have htK : t ∈ K := hYK ht
      refine hOK ⟨?_, ?_⟩
      · have h1 : t * v⁻¹ * t⁻¹ ∈ pCoreOf 2 H :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hKH htK)) _).mp
            (Subgroup.inv_mem _ hvO)
        rw [commutatorElement_def]
        have e1 : v * t * v⁻¹ * t⁻¹ = v * (t * v⁻¹ * t⁻¹) := by group
        rw [e1]
        exact Subgroup.mul_mem _ hvO h1
      · have h1 : v * t * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hON hvO) t).mp htK
        rw [commutatorElement_def]
        exact K.mul_mem h1 (K.inv_mem htK)
    have hvmc : S.vm e ≤ ⁅S.vm e, Y⁆ := vm_le_commutator hc hm hyN
    have hvmK : S.vm e ≤ pCoreOf 2 K := hvmc.trans hcomm
    have hvmU : S.vm e ≤ blockU K := hvmc.trans (Subgroup.commutator_mono hvmK hYK)
    have hZK : blockZ K ≤ Subgroup.centralizer (K : Set G) := inf_le_right
    have hvmZ : S.vm e ⊓ blockZ K = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have h1 : y * v = v * y := Subgroup.mem_centralizer_iff.mp (hZK hv.2) y hW.y_mem
      exact (Subgroup.mem_bot).2 (eq_one_of_mem_vm hc hm hv.1 h1)
    have hvmN : S.vm e ≤ Subgroup.normalizer (blockZ K : Set G) := fun v hv =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
        (Subgroup.mem_centralizer_iff.mp (hZK hz) v ((pCoreOf_le 2 K) (hvmK hv))).symm)
    have hsup : S.vm e ⊔ blockZ K = blockU K := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hvmU inf_le_left) ?_
      have h1 := Lin2.card_sup_mul_card_inf hvmN
      rw [hvmZ, Subgroup.card_bot, mul_one, card_vm] at h1
      rw [hcard, h1]
    apply hQK
    intro s hs
    refine hfaith s hs.2 fun u hu => ?_
    have hle : blockU K ≤ Subgroup.centralizer ({s} : Set G) := by
      rw [← hsup]
      refine sup_le (fun v hv => ?_) (fun z hz => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hs.1.2 v (vm_le hv)))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp (hZK hz) s hs.2).symm)
    have h1 : s * u = u * s := (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm
    have e1 : s * u * s⁻¹ * u⁻¹ = 1 := by rw [h1]; group
    rw [e1]
    exact Subgroup.one_mem _
  ·
    set A := Y ⊓ Subgroup.centralizer (fsuV T I : Set G) with hAdef
    have hAc : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2.1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2.1
      change (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])⟩⟩
    have hAo : Odd (Nat.card A) := Odd.of_dvd_nat hYo (Subgroup.card_dvd_of_le inf_le_left)
    have hNA := S.normalizer_le h443 (inf_le_left.trans hYM) inf_le_right hA hAc hAo
    have hwN : w ∈ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      le_normalizer_pCoreOf 2 K hW.w_mem
    have hAN : A ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      (inf_le_left.trans hYK).trans (le_normalizer_pCoreOf 2 K)
    have hwA : ∀ a ∈ A, w * a * w⁻¹ ∈ pCoreOf 2 K ⊔ A := by
      intro a ha
      obtain ⟨n, rfl⟩ : ∃ n : ℕ, y ^ n = a :=
        (mem_powers_iff_mem_zpowers).mpr ha.1
      have h1 := hW.inv n
      have e1 : w * y ^ n * w⁻¹ = (w * y ^ n * w⁻¹ * y ^ n) * (y ^ n)⁻¹ := by group
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (A.inv_mem ha))
    obtain ⟨z, hz, hzw⟩ := exists_mem_normalizer_of_conj_le hAo (pCoreOf_isPGroup 2 K) hAN hwN hwA
    have hwM : w ∈ fsuM T L := by
      have h1 : z * w ∈ fsuM T L := hNA hzw
      have h2 : z⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (hO2M hz)
      have := (fsuM T L).mul_mem h2 h1
      simpa using this
    exact hW.w_not (hB1 ⟨hW.w_mem, hwM⟩)

theorem false_of_sylow (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L)
    (hSyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K) K) : False := by
  have hyp := C.hypC23
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  rcases hC24a H _ _ K hyp hK hK2 hKq hSyl with hKMH | ⟨hchi, -, hBor⟩
  · exact hKM (hKMH.trans inf_le_left)
  have hKMeq : K ⊓ (fsuM T L ⊓ H) = K ⊓ fsuM T L := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hKH h.1⟩⟩
  have h3 : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≠ 3 := card_ne_three_of_isQuasisimple hKq
  unfold IsBorelOfBlock at hBor
  rw [ite_eq_right h3, hKMeq] at hBor
  obtain ⟨P, hP, hSeq⟩ := hBor
  have hB1 : K ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G) :=
    le_sup_left.trans (hSeq.le.trans inf_le_right)
  have hB2 : K ⊓ Subgroup.normalizer (P : Set G) ≤ fsuM T L := by
    rw [← hSeq]
    exact sup_le inf_le_right (C.pCoreOf_le_fsuM hK)
  obtain ⟨-, htype⟩ := hchi
  rcases htype with ⟨n, hn, hlin⟩ | h3' | h5
  · exact C.false_of_block h443 hF hK (Or.inl ⟨n, hn, hlin⟩) hP hB1 hB2
      (not_le_pCoreOf_lin2 (by omega) hlin hSyl)
  · exact h3 (card_quot_of_isAltType_three h3')
  · exact C.false_of_block h443 hF hK (Or.inr h5) hP hB1 hB2 (not_le_pCoreOf_alt5 h5 hSyl)

theorem Q_le_normalizer (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hC24b : ASC24TwoChar G)
    (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L) :
    T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  by_contra hQ
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  exact C.false_of_sylow h443 hC24a hF hK hKq hKM
    ((hC24b H _ _ K C.hypC23 hF hK hK2 hKq).resolve_right hQ)

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
