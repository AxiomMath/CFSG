module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompA
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6Aut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.Adapters.LinearSmallCatalog

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

section Perm

variable {n : ℕ}

theorem cycleType_eq_replicate_of_sq {σ : Perm (Fin n)} (h2 : σ ^ 2 = 1) :
    σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 := by
  rw [Multiset.eq_replicate]
  refine ⟨rfl, fun m hm => ?_⟩
  have h1 := two_le_of_mem_cycleType hm
  have h3 : m ∣ 2 := (dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one h2)
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem card_centralizer_involution {σ : Perm (Fin n)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1) :
    1 ≤ Multiset.card σ.cycleType ∧ 2 * Multiset.card σ.cycleType ≤ n ∧
      Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) =
        (n - 2 * Multiset.card σ.cycleType).factorial * 2 ^ Multiset.card σ.cycleType *
          (Multiset.card σ.cycleType).factorial := by
  have hct := cycleType_eq_replicate_of_sq h2
  set k := Multiset.card σ.cycleType with hk
  have hk1 : 1 ≤ k := by
    rw [hk, Nat.one_le_iff_ne_zero, Ne, card_cycleType_eq_zero]
    exact h1
  have hsum : σ.cycleType.sum = 2 * k := by
    rw [hct, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hle : 2 * k ≤ n := by
    have := sum_cycleType_le σ
    rw [hsum, Fintype.card_fin] at this
    exact this
  refine ⟨hk1, hle, ?_⟩
  have htf : (Multiset.replicate k 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]
    split_ifs with h0
    · omega
    · rfl
  rw [nat_card_centralizer, Fintype.card_fin, hsum, hct, Multiset.prod_replicate, htf,
    Finset.prod_singleton, Multiset.count_replicate_self]

theorem sign_of_card_cycleType_one {σ : Perm (Fin n)} (h2 : σ ^ 2 = 1)
    (h1 : Multiset.card σ.cycleType = 1) : σ ∉ alternatingGroup (Fin n) := by
  rw [mem_alternatingGroup, sign_of_cycleType, cycleType_eq_replicate_of_sq h2, h1]
  decide

end Perm

theorem exists_elemAbelian_nine {G : Type*} [Group G] [Finite G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hind : ∀ i j : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = 1 → i = 0 ∧ j = 0) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  classical
  have ha1 : a ≠ 1 := fun h1 => by
    have := hind 1 0 (by simp [h1])
    exact absurd this.1 (by decide)
  have hb1 : b ≠ 1 := fun h1 => by
    have := hind 0 1 (by simp [h1])
    exact absurd this.2 (by decide)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb hb1
  have hcomm : ∀ (x : ↥(Subgroup.zpowers a)) (y : ↥(Subgroup.zpowers b)),
      Commute ((Subgroup.zpowers a).subtype x) ((Subgroup.zpowers b).subtype y) := by
    intro x y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change Commute (x : G) (y : G)
    rw [← hm, ← hk]
    exact Commute.zpow_zpow hab m k
  let f : ↥(Subgroup.zpowers a) × ↥(Subgroup.zpowers b) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype hcomm
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp x.2)
    obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp y.2)
    rw [hoa, Finset.mem_range] at hi
    rw [hob, Finset.mem_range] at hj
    rw [← hix, ← hjy] at hxy'
    obtain ⟨hi0, hj0⟩ := hind ⟨i, hi⟩ ⟨j, hj⟩ hxy'
    have hi0' : i = 0 := congrArg Fin.val hi0
    have hj0' : j = 0 := congrArg Fin.val hj0
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [← hix, hi0', pow_zero]
      rfl
    · rw [← hjy, hj0', pow_zero]
      rfl
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨p, hp⟩ := x.2
    obtain ⟨q, hq⟩ := y.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hq, ← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp p.1.2
      obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp q.1.2
      change (p.1 : G) * q.1 = q.1 * p.1
      rw [← hm, ← hm']
      exact (Commute.zpow_zpow_self a m m').eq
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp p.2.2
      obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp q.2.2
      change (p.2 : G) * q.2 = q.2 * p.2
      rw [← hm, ← hm']
      exact (Commute.zpow_zpow_self b m m').eq
  · rintro _ ⟨⟨u, w⟩, rfl⟩
    rw [← map_pow]
    have : (u, w) ^ 3 = 1 := by
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp u.2
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp w.2
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change (u : G) ^ 3 = 1
        rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]
      · change (w : G) ^ 3 = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]
    rw [this, map_one]
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hf, Subgroup.card_top,
      Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hoa, hob]

theorem card_eq_of_isSylowTwoOf {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsSylowTwoOf S ⊤) {a m : ℕ} (hG : Nat.card G = 2 ^ a * m) (hm : Odd m) :
    Nat.card S = 2 ^ a := by
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hS.2.1
  have hidx : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at this
  have heq : 2 ^ b * S.index = 2 ^ a * m := by rw [← hb, S.card_mul_index, hG]
  rw [hb]
  rcases lt_trichotomy b a with hba | rfl | hab
  · exfalso
    apply hidx
    have h1 : 2 ^ b * 2 ∣ 2 ^ b * S.index := by
      rw [heq, ← pow_succ]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hba) m
    exact (Nat.mul_dvd_mul_iff_left (pow_pos two_pos b)).mp h1
  · rfl
  · exfalso
    apply Nat.not_even_iff_odd.mpr hm
    have h1 : 2 ^ a * 2 ∣ 2 ^ a * m := by
      rw [← heq, ← pow_succ]
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hab) _
    exact even_iff_two_dvd.mpr ((Nat.mul_dvd_mul_iff_left (pow_pos two_pos a)).mp h1)

section Alt

variable {n : ℕ} {ν : MulAut (alternatingGroup (Fin n))}
  {Lb Pb : Subgroup (MulAut (alternatingGroup (Fin n)))}

theorem bijective_conjNormal (hn : 5 ≤ n) (hn6 : n ≠ 6) :
    Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
      Perm (Fin n) →* MulAut (alternatingGroup (Fin n))) :=
  CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6

theorem AutConf.exists_perm (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (h : AutConf (alternatingGroup (Fin n)) ν Lb Pb) :
    ∃ σ : Perm (Fin n), MulAut.conjNormal σ = ν ∧ σ ^ 2 = 1 ∧ σ ≠ 1 := by
  have hb := bijective_conjNormal hn hn6
  obtain ⟨σ, rfl⟩ := hb.2 ν
  refine ⟨σ, rfl, hb.1 ?_, fun h1 => h.ne_one ?_⟩
  · rw [map_pow, h.sq, map_one]
  · rw [h1, map_one]

theorem AutConf.mem_centralizer (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (h : AutConf (alternatingGroup (Fin n)) ν Lb Pb) {σ : Perm (Fin n)}
    (hσ : MulAut.conjNormal σ = ν) {τ : Perm (Fin n)} (hτ : MulAut.conjNormal τ ∈ Lb) :
    τ ∈ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply (bijective_conjNormal hn hn6).1
  rw [map_mul, map_mul, hσ]
  exact h.comm _ hτ

theorem AutConf.fix_mem_centralizer {σ : Perm (Fin n)}
    (hσ : MulAut.conjNormal σ = ν) {s : alternatingGroup (Fin n)} (hs : ν s = s) :
    (s : Perm (Fin n)) ∈ Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := congrArg Subtype.val hs
  rw [← hσ, MulAut.conjNormal_apply] at h1
  calc (s : Perm (Fin n)) * σ = σ * s * σ⁻¹ * σ := by rw [h1]
    _ = σ * s := by group

theorem not_autConf_alt78 (hn : n = 7 ∨ n = 8) (h : AutConf (alternatingGroup (Fin n)) ν Lb Pb)
    (h9 : Nat.card Pb = 9) : False := by
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  have hb := bijective_conjNormal hn5 hn6
  obtain ⟨σ, hσ, hσ2, hσ1⟩ := h.exists_perm hn5 hn6
  have hE : Nat.card (Pb.comap (MulAut.conjNormal (H := alternatingGroup (Fin n)))) = 9 := by
    rw [← Subgroup.card_map_of_injective hb.1, Subgroup.map_comap_eq_self_of_surjective hb.2, h9]
  have hEC : Pb.comap (MulAut.conjNormal (H := alternatingGroup (Fin n))) ≤
      Subgroup.centralizer ({σ} : Set (Perm (Fin n))) := fun τ hτ =>
    h.mem_centralizer hn5 hn6 hσ (h.le hτ)
  obtain ⟨hk1, hk, hcard⟩ := card_centralizer_involution hσ2 hσ1
  have h9d : 9 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin n)))) :=
    hE ▸ Subgroup.card_dvd_of_le hEC
  rw [hcard] at h9d
  generalize Multiset.card σ.cycleType = k at hk1 hk hcard h9d
  rcases hn with rfl | rfl
  · have hk4 : k ≤ 3 := by omega
    interval_cases k <;> norm_num [Nat.factorial] at h9d
  · have hk4 : k ≤ 4 := by omega
    interval_cases k
    ·
      obtain ⟨S, hS, hSν⟩ := h.sylow
      have hcardA : Nat.card (alternatingGroup (Fin 8)) = 2 ^ 6 * 315 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
        decide
      have hS64 := card_eq_of_isSylowTwoOf hS hcardA (by decide)
      have hSC : S.map (alternatingGroup (Fin 8)).subtype ≤
          Subgroup.centralizer ({σ} : Set (Perm (Fin 8))) := by
        rintro _ ⟨s, hs, rfl⟩
        exact AutConf.fix_mem_centralizer hσ (hSν s hs)
      have h64 := Subgroup.card_dvd_of_le hSC
      rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 8)).subtype_injective, hS64,
        hcard] at h64
      norm_num [Nat.factorial] at h64
    all_goals norm_num [Nat.factorial] at h9d

theorem not_autConf_alt5 {ν : MulAut (alternatingGroup (Fin 5))}
    {Lb Pb : Subgroup (MulAut (alternatingGroup (Fin 5)))}
    (h : AutConf (alternatingGroup (Fin 5)) ν Lb Pb) : False := by
  have hb := bijective_conjNormal (n := 5) (by norm_num) (by norm_num)
  obtain ⟨σ, hσ, hσ2, hσ1⟩ := h.exists_perm (by norm_num) (by norm_num)
  obtain ⟨hk1, hk, hcard⟩ := card_centralizer_involution hσ2 hσ1
  have hodd := sign_of_card_cycleType_one hσ2
  generalize hkk : Multiset.card σ.cycleType = k at hk1 hk hcard hodd
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  ·
    obtain ⟨S, hS, hSν⟩ := h.sylow
    have hcardA : Nat.card (alternatingGroup (Fin 5)) = 2 ^ 2 * 15 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    have hS4 := card_eq_of_isSylowTwoOf hS hcardA (by decide)
    set C := Subgroup.centralizer ({σ} : Set (Perm (Fin 5))) with hC
    have hσC : σ ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hσA := hodd rfl
    have hrel : (alternatingGroup (Fin 5)).relIndex C = 2 := by
      have hd := Subgroup.relIndex_dvd_index_of_normal (alternatingGroup (Fin 5)) C
      rw [alternatingGroup.index_eq_two] at hd
      have h1 : (alternatingGroup (Fin 5)).relIndex C ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        exact fun hle => hσA (hle hσC)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h' | h'
      · exact absurd h' h1
      · exact h'
    have hcAC : Nat.card ((alternatingGroup (Fin 5)).subgroupOf C) = 6 := by
      have h1 := ((alternatingGroup (Fin 5)).subgroupOf C).card_mul_index
      rw [show ((alternatingGroup (Fin 5)).subgroupOf C).index =
        (alternatingGroup (Fin 5)).relIndex C from rfl, hrel, hcard] at h1
      norm_num [Nat.factorial] at h1
      omega
    have hSC : S.map (alternatingGroup (Fin 5)).subtype ≤ C := by
      rintro _ ⟨s, hs, rfl⟩
      exact AutConf.fix_mem_centralizer hσ (hSν s hs)
    have hSA : (S.map (alternatingGroup (Fin 5)).subtype).subgroupOf C ≤
        (alternatingGroup (Fin 5)).subgroupOf C := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨s, -, hs⟩ := hx
      rw [← hs]
      exact s.2
    have h1 := Subgroup.card_dvd_of_le hSA
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv,
      Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective, hS4,
      hcAC] at h1
    norm_num at h1
  ·
    apply h.ne_bot
    rw [← h.gen, eq_bot_iff]
    refine (Subgroup.closure_le _).mpr fun l hl => ?_
    obtain ⟨τ, rfl⟩ := hb.2 l
    have hτC := h.mem_centralizer (by norm_num) (by norm_num) hσ hl.1
    have h3 : τ ^ 3 = 1 := hb.1 (by rw [map_pow, h.three _ hl.1 hl.2, map_one])
    have h8 : τ ^ 8 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.centralizer ({σ} : Set (Perm (Fin 5))))
        (x := ⟨τ, hτC⟩)
      rw [hcard] at this
      norm_num [Nat.factorial] at this
      exact this
    have h1 : τ = 1 := by
      have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h8)
      norm_num at hd
      exact hd
    rw [h1, map_one, SetLike.mem_coe]
    exact one_mem _

end Alt

theorem mul_conj_mul_inv' {M : Type*} [Group M] (φ : MulAut M) (x : M) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) :=
  MulEquiv.ext fun y => by
    change φ (x * φ.symm y * x⁻¹) = φ x * y * (φ x)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem index_gt_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] {F : Subgroup G}
    (hF : F ≠ ⊤) {n : ℕ} (hn : F.index ≤ n) : Nat.card G ≤ n.factorial := by
  have hcore : F.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.mp (h ▸ F.normalCore_le)) hF
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ F)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card] at this
  exact this.trans (Nat.factorial_le hn)

theorem not_autConf_alt6 {ν : MulAut (alternatingGroup (Fin 6))}
    {Lb Pb : Subgroup (MulAut (alternatingGroup (Fin 6)))}
    (h : AutConf (alternatingGroup (Fin 6)) ν Lb Pb) (h9 : Nat.card Pb = 9) : False := by
  have hinj :=
    CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  have hPin : Pb ≤ (MulAut.conj : alternatingGroup (Fin 6) →* _).range := fun π hπ =>
    CFSG.RankThree.PartTwo.Sec14.Item148PtRes.mem_inner_of_pow_three (h.elem.2 π hπ)
  have hE : Nat.card (Pb.comap (MulAut.conj : alternatingGroup (Fin 6) →* _)) = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hPin, h9]
  set F := MonoidHom.eqLocus ν.toMonoidHom (MonoidHom.id (alternatingGroup (Fin 6))) with hFdef
  have hEF : Pb.comap (MulAut.conj : alternatingGroup (Fin 6) →* _) ≤ F := fun x hx => by
    have hc := h.comm _ (h.le hx)
    have h1 : MulAut.conj (ν x) = MulAut.conj x := by
      rw [← mul_conj_mul_inv', ← hc, mul_inv_cancel_right]
    exact hinj h1
  obtain ⟨S, hS, hSν⟩ := h.sylow
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 2 ^ 3 * 45 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hS8 := card_eq_of_isSylowTwoOf hS hcardA (by decide)
  have hSF : S ≤ F := fun s hs => hSν s hs
  have h72 : 72 ∣ Nat.card F :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 8)
      (hE ▸ Subgroup.card_dvd_of_le hEF)
      (by rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← hS8]; exact Subgroup.card_dvd_of_le hSF)
  have hFtop : F = ⊤ := by
    by_contra hF
    have := alternatingGroup.isSimpleGroup (α := Fin 6) (by simp)
    have hidx : F.index ≤ 5 := by
      have h1 := F.card_mul_index
      rw [hcardA] at h1
      obtain ⟨c, hc⟩ := h72
      rw [hc] at h1
      have hc0 : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0] at h1; omega
        · exact h0
      have : 72 * F.index ≤ 360 := by nlinarith
      omega
    have := index_gt_of_simple hF hidx
    rw [hcardA] at this
    norm_num [Nat.factorial] at this
  apply h.ne_one
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ F := hFtop ▸ Subgroup.mem_top x
  exact hx

theorem eq_one_of_mem_center_alt {n : ℕ} (hn : 4 ≤ n) {z : alternatingGroup (Fin n)}
    (hz : z ∈ Subgroup.center (alternatingGroup (Fin n))) : z = 1 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn
  have h1 : MulAut.conjNormal (H := alternatingGroup (Fin n)) (z : Perm (Fin n)) = 1 :=
    MulEquiv.ext fun x => Subtype.ext (by
      rw [MulAut.conjNormal_apply]
      have := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz x)
      simp only [Subgroup.coe_mul] at this
      change (z : Perm (Fin n)) * x * (z : Perm (Fin n))⁻¹ = x
      rw [← this, mul_inv_cancel_right])
  exact Subtype.ext (hinj (h1.trans (map_one _).symm))

theorem exists_E9_alt6 :
    ∃ E : Subgroup (alternatingGroup (Fin 6)), IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  exists_elemAbelian_nine (a := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩)
    (b := ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩) (by decide) (by decide)
    (by decide) (by decide)

theorem exists_E9_alt7 :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  exists_elemAbelian_nine (a := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩)
    (b := ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩) (by decide) (by decide)
    (by decide) (by decide)

theorem exists_E9_alt8 :
    ∃ E : Subgroup (alternatingGroup (Fin 8)), IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  exists_elemAbelian_nine (a := ⟨swap 0 1 * swap 1 2, by rw [mem_alternatingGroup]; decide⟩)
    (b := ⟨swap 3 4 * swap 4 5, by rw [mem_alternatingGroup]; decide⟩) (by decide) (by decide)
    (by decide) (by decide)

@[expose] def Comp12626Alt : Prop :=
  ∀ (Q : Type) [Group Q] (K L P T : Subgroup Q) (v : Q), Vol2Native.SQTKHypCat Q →
    Conf12626 K L P T v →
      ¬ ((∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (↥K ≃* alternatingGroup (Fin n))) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥K .PSL 2 2 2)

theorem Conf12626.card_map_rhoP_eq_nine {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}
    (hQ : Vol2Native.SQTKHypCat Q) (h : Conf12626 K L P T v) {M : Type} [Group M]
    (e : ↥K ≃* M) (hZ : ∀ z ∈ Subgroup.center M, z = 1) {E : Subgroup M}
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    Nat.card (h.rhoP.range.map (MulAut.congr e).toMonoidHom) = 9 := by
  have := hQ.finite
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
  refine h.card_rhoP_range_eq_nine hQ (E := E.map e.symm.toMonoidHom) ?_ ?_ fun z hz _ => ?_
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx, hxa⟩ := a.2
      obtain ⟨y, hy, hyb⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul]
      exact congrArg (fun w : ↥E => e.symm.toMonoidHom w) (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hE9]
  · have hz' : e z ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro y
      rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz]
    have := hZ _ hz'
    rw [← e.symm_apply_apply z, this, map_one]

theorem comp12626Alt_holds : Comp12626Alt := by
  intro Q _ K L P T v hQ h hK
  have := hQ.finite
  rcases hK with ⟨n, hn5, hn8, ⟨e⟩⟩ | hL24
  · have hA := h.autConf.map e
    interval_cases n
    · exact not_autConf_alt5 hA
    · obtain ⟨E, hE, hE9⟩ := exists_E9_alt6
      exact not_autConf_alt6 hA (h.card_map_rhoP_eq_nine hQ e
        (fun z hz => eq_one_of_mem_center_alt (by norm_num) hz) hE hE9)
    · obtain ⟨E, hE, hE9⟩ := exists_E9_alt7
      exact not_autConf_alt78 (Or.inl rfl) hA (h.card_map_rhoP_eq_nine hQ e
        (fun z hz => eq_one_of_mem_center_alt (by norm_num) hz) hE hE9)
    · obtain ⟨E, hE, hE9⟩ := exists_E9_alt8
      exact not_autConf_alt78 (Or.inr rfl) hA (h.card_map_rhoP_eq_nine hQ e
        (fun z hz => eq_one_of_mem_center_alt (by norm_num) hz) hE hE9)
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hL24
    obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inl (by rw [hF]; norm_num))
    exact not_autConf_alt5 (h.autConf.map (e.trans e'))

end CFSG.Quasithin.H13.S126C
