module

public import CFSG.Quasithin.Vol2.KGFactC31HeChains
public import CFSG.Quasithin.Vol2.KGFactC31M24Sx
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.Vol2.KGFactC31HeR

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  _root_.Certificates

theorem no_o2_16 : ∀ m ∈ Ch1.SporLat.He.heMems, m.o2 ≠ 16 := by
  intro m hm
  simp only [Ch1.SporLat.He.heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem order_of_o2_64 : ∀ m ∈ Ch1.SporLat.He.heMems, m.o2 = 64 → m.order = 138240 := by
  intro m hm
  simp only [Ch1.SporLat.He.heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem prime_eq_five {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (h : p ∣ 138240) : p = 5 := by
  have h' : p ∣ 2 ^ 10 * 3 ^ 3 * 5 := by norm_num; exact h
  rcases (Nat.Prime.dvd_mul hp).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2); omega
  · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1

theorem exists_orderOf_eq_pow {G : Type*} [Group G] {y : G} {p k : ℕ} (hp : p.Prime)
    (hyk : y ^ p ^ k = 1) (hy1 : y ≠ 1) : ∃ j, 0 < j ∧ orderOf y = p ^ j := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hyk)
  refine ⟨j, Nat.pos_of_ne_zero fun h0 => hy1 ?_, hj⟩
  rw [h0, pow_zero, orderOf_eq_one_iff] at hj
  exact hj

variable {A : Type} [Group A]

theorem comap_le_normalizer {ι : A →* Equiv.Perm (Fin 8330)}
    {Y Z : Subgroup (Equiv.Perm (Fin 8330))}
    (hYZ : Y ≤ Subgroup.normalizer (Z : Set (Equiv.Perm (Fin 8330)))) :
    Y.comap ι ≤ Subgroup.normalizer ((Z.comap ι : Subgroup A) : Set A) := by
  intro x hx
  refine Subgroup.mem_normalizer_iff.mpr fun r => ?_
  have h := Subgroup.mem_normalizer_iff.mp (hYZ hx) (ι r)
  simp only [Subgroup.mem_comap, map_mul, map_inv] at h ⊢
  exact h

theorem Emb.exists_of_mem {S : Subgroup A} {ι : A →* Equiv.Perm (Fin 8330)} (hι : Emb S ι)
    {x : Equiv.Perm (Fin 8330)} (hx : x ∈ heP) : ∃ a ∈ S, ι a = x := by
  rw [← hι.mapS] at hx
  exact Subgroup.mem_map.mp hx

theorem vW5_mem_E (i : Fin 4) :
    vW5 i ∈ eSub basis_E := by
  rw [vW5_eq]
  exact mem_eSub basis_E _

@[expose] noncomputable def lsAct :
    ↥lGrp →* Equiv.Perm (Fin 6) :=
  (blockAct bBlk_inj).comp (Subgroup.inclusion Ls_le_blockStab)

theorem lsAct_eq_one_iff
    (x : ↥lGrp) : lsAct x = 1 ↔ (x : Equiv.Perm (Fin 8330)) ∈ bFix := by
  rw [lsAct, MonoidHom.comp_apply, blockAct_eq_one_iff, mem_bFix]
  simp only [bBlk, Finset.image_singleton, Finset.singleton_inj, Subgroup.coe_inclusion]

theorem card_ker_lsAct :
    Nat.card lsAct.ker = 192 := by
  rw [← card_fix_Ls]
  exact Nat.card_congr
    { toFun := fun x => ⟨x.1, (lsAct_eq_one_iff x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (lsAct_eq_one_iff x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem ls_alt_data
    (hperf : ⁅lGrp, lGrp⁆ = lGrp) :
    ∃ ψ : ↥lGrp →* ↥(alternatingGroup (Fin 6)), Function.Surjective ψ ∧
      Nat.card ψ.ker = 192 ∧
      ∀ x : ↥lGrp, (x : Equiv.Perm (Fin 8330)) ∈ bFix → ψ x = 1 := by
  have hcommK : commutator ↥lGrp = ⊤ := by
    apply Subgroup.map_injective lGrp.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hperf]
  have hsign : ∀ x, Equiv.Perm.sign (lsAct x) = 1 := by
    intro x
    have h1 : x ∈ (Equiv.Perm.sign.comp lsAct).ker := by
      have := Abelianization.commutator_subset_ker (Equiv.Perm.sign.comp lsAct)
      rw [hcommK] at this
      exact this (Subgroup.mem_top x)
    exact h1
  let ψ : ↥lGrp →* ↥(alternatingGroup (Fin 6)) :=
    lsAct.codRestrict _ fun x => Equiv.Perm.mem_alternatingGroup.mpr (hsign x)
  have hker : ψ.ker = lsAct.ker := MonoidHom.ker_codRestrict _ _ _
  refine ⟨ψ, ?_, by rw [hker, card_ker_lsAct], fun x hx => ?_⟩
  · rw [← MonoidHom.range_eq_top]
    apply Subgroup.eq_top_of_card_eq
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hker, card_ker_lsAct, card_Ls] at h1
    rw [M24.card_alt6]
    omega
  · have : x ∈ ψ.ker := by
      rw [hker]
      exact (lsAct_eq_one_iff x).mpr hx
    exact this

variable [Finite A] {S M₀ R M V : Subgroup A} {ι : A →* Equiv.Perm (Fin 8330)}

theorem false_w7
    (h : Setup S M₀ R M V) (hι : Emb S ι) (hW : ∀ i, vW7 i ∈ V.map ι) :
    False := by
  have hR := R_eq_of_ref h hι basis_Q (fun x hx => Q_le_heP hx)
    (fun x hx hc => mem_Q_of_cent hx hc) hW
  have hRc : Nat.card R = 16 := by rw [hR, hι.card_comap Q_le_heP, card_eSub]; norm_num
  have hN7P : n7Grp ≤ heP := N7_le.trans inf_le_left
  obtain ⟨m, hm, -, ho2⟩ := exists_mem_heMems h.hS h.hSs h.hR2
    (by rw [hR]; exact hι.comap_le_S Q_le_heP) h.R_ne_bot h.hrad
    (X := n7Grp.comap ι)
    (by rw [hR]; exact comap_le_normalizer (N7_le.trans inf_le_right))
    (hι.comap_le_S hN7P) (by rw [hι.card_comap hN7P, card_N7]; norm_num)
  exact no_o2_16 m hm (by rw [← ho2, hRc])

theorem concl_w5
    (h : Setup S M₀ R M V) (hM₀S : M₀ ≤ S) (hι : Emb S ι)
    (hW : ∀ i, vW5 i ∈ V.map ι) {y : A} (hy : y ∈ M₀) {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hyk : y ^ p ^ k = 1) (hy1 : y ≠ 1) : Concl S M₀ R M V := by
  have hR := R_eq_of_ref h hι basis_E (fun x hx => E_le_heP hx)
    (fun x hx hc => mem_E_of_cent hx hc) hW
  have hmemR : ∀ x, x ∈ R ↔ ι x ∈ eSub basis_E := fun x => by rw [hR, Subgroup.mem_comap]
  have hRc : Nat.card R = 64 := by rw [hR, hι.card_comap E_le_heP, card_eSub]; norm_num
  set N' := Subgroup.normalizer (R : Set A) ⊓ S with hN'
  have hNsP : nsGrp ≤ heP := Ns_le.trans inf_le_left
  have hEN : (eNorm basis_E).comap ι ≤ Subgroup.normalizer (R : Set A) := by
    rw [hR]
    exact comap_le_normalizer le_rfl
  obtain ⟨m, hm, hord, ho2⟩ := exists_mem_heMems h.hS h.hSs h.hR2
    (by rw [hR]; exact hι.comap_le_S E_le_heP) h.R_ne_bot h.hrad
    (X := nsGrp.comap ι)
    ((Subgroup.comap_mono (Ns_le.trans inf_le_right)).trans hEN)
    (hι.comap_le_S hNsP) (by rw [hι.card_comap hNsP, card_Ns]; norm_num)
  have hNc : Nat.card N' = 138240 := by
    rw [hord]
    exact order_of_o2_64 m hm (by rw [← ho2, hRc])
  have hM₀N : M₀ ≤ N' := le_inf h.hM₀R hM₀S
  have hnorm : N' ≤ Subgroup.normalizer (M₀ : Set A) := inf_le_left.trans h.normal_in_normalizer
  have hp5' : p = 5 := by
    obtain ⟨j, hj, hoy⟩ := exists_orderOf_eq_pow hp hyk hy1
    have h1 : orderOf y ∣ Nat.card N' := by
      have := orderOf_dvd_natCard (⟨y, hM₀N hy⟩ : ↥N')
      rwa [Subgroup.orderOf_mk] at this
    rw [hoy, hNc] at h1
    exact prime_eq_five hp hp5 ((dvd_pow_self p hj.ne').trans h1)
  subst hp5'
  set Ls := lGrp with hLs
  have hLsP : Ls ≤ heP := Ls_le.trans inf_le_left
  have hLsN : Ls.comap ι ≤ N' :=
    le_inf ((Subgroup.comap_mono (Ls_le.trans inf_le_right)).trans hEN) (hι.comap_le_S hLsP)
  have hi : (Ls.comap ι).relIndex N' ≤ 4 := by
    have h1 := (Ls.comap ι).relIndex_mul_card (K := N')
    rw [inf_eq_left.mpr hLsN, hNc, hι.card_comap hLsP, card_Ls] at h1
    omega
  have hM₀Ls : M₀ ≤ Ls.comap ι := le_of_perfect_of_relIndex_le hM₀N h.hper hi
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, haS, hay⟩ := hι.exists_of_mem (hLsP y5_mem_Ls)
  have haN : a ∈ N' := hLsN (by rw [Subgroup.mem_comap, hay]; exact y5_mem_Ls)
  have hoa : orderOf a = 5 := by rw [← orderOf_injective ι hι.inj, hay, orderOf_y5]
  have hNp : ¬ 5 ^ 2 ∣ Nat.card N' := by rw [hNc]; norm_num
  have haM : a ∈ M₀ := M24.mem_of_sylow haN hoa hNp hM₀N hnorm hy ⟨k, hyk⟩ hy1
  have hLsM : Ls ≤ M₀.map ι := by
    rw [hLs, Ls_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    rcases mem_lsGenW hw with rfl | ⟨n, hn, rfl⟩
    · exact ⟨a, haM, hay⟩
    · obtain ⟨b, hbS, hb⟩ := hι.exists_of_mem
        (elt_mem_heP (List.all_eq_true.1 letters_njW n hn))
      have hbN : b ∈ N' := ⟨hEN (by rw [Subgroup.mem_comap, hb]; exact nj_mem_eNorm hn), hbS⟩
      refine ⟨b * a * b⁻¹, (Subgroup.mem_normalizer_iff.mp (hnorm hbN) a).mp haM, ?_⟩
      rw [map_mul, map_mul, map_inv, hb, hay, elt_lsGen hn]
  have hM₀eq : M₀ = Ls.comap ι := le_antisymm hM₀Ls (by
    have := Subgroup.comap_mono (f := ι) hLsM
    rwa [Subgroup.comap_map_eq_self_of_injective hι.inj] at this)
  have hmap : M₀.map ι = Ls := by rw [hM₀eq]; exact hι.map_comap hLsP
  have hRM₀ : R ≤ M₀ := by
    rw [hR, hM₀eq]
    exact Subgroup.comap_mono E_le_Ls
  have hcM₀ : Nat.card M₀ = 69120 := by rw [hM₀eq, hι.card_comap hLsP, card_Ls]
  have hLsperf : ⁅Ls, Ls⁆ = Ls := by
    rw [← hmap, ← Subgroup.map_commutator, h.hper]
  obtain ⟨ψ₀, hψs, hψk, hψR⟩ := ls_alt_data hLsperf
  let e : ↥Ls ≃* ↥M₀ :=
    ((M₀.equivMapOfInjective ι hι.inj).trans (MulEquiv.subgroupCongr hmap)).symm
  have he : ∀ x : ↥M₀, ((e.symm x : ↥Ls) : Equiv.Perm (Fin 8330)) = ι x := fun _ => rfl
  let ψ : ↥M₀ →* ↥(alternatingGroup (Fin 6)) := ψ₀.comp e.symm.toMonoidHom
  have hψsurj : Function.Surjective ψ := hψs.comp e.symm.surjective
  have hψker : ψ.ker = ψ₀.ker.map e.toMonoidHom := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨e.symm x, hx, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      show ψ₀ (e.symm (e z)) = 1
      rw [MulEquiv.symm_apply_apply]
      exact hz
  have hψk' : Nat.card ψ.ker = 192 := by
    rw [hψker, Subgroup.card_map_of_injective e.injective, hψk]
  have hRle : R.subgroupOf M₀ ≤ ψ.ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, hmemR] at hx
    rw [MonoidHom.mem_ker]
    show ψ₀ (e.symm x) = 1
    exact hψR _ (by rw [he]; exact E_le_bFix hx)
  have hRn : (R.subgroupOf M₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM₀).mpr h.hM₀R
  let φ : ↥M₀ ⧸ R.subgroupOf M₀ →* ↥(alternatingGroup (Fin 6)) := QuotientGroup.lift _ ψ hRle
  have hφs : Function.Surjective φ := by
    intro σ
    obtain ⟨x, hx⟩ := hψsurj σ
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk]; exact hx⟩
  have hRMc : Nat.card (R.subgroupOf M₀) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM₀).toEquiv, hRc]
  have hcq : Nat.card (↥M₀ ⧸ R.subgroupOf M₀) = 1080 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (R.subgroupOf M₀)
    rw [hcM₀, hRMc] at this
    omega
  have hφk : Nat.card φ.ker = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      M24.card_alt6, hcq] at h1
    omega
  have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hperfQ : commutator (↥M₀ ⧸ R.subgroupOf M₀) = ⊤ := by
    have hcommM : commutator ↥M₀ = ⊤ := by
      apply Subgroup.map_injective M₀.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, h.hper]
    rw [commutator_def, ← Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective (R.subgroupOf M₀)), ← Subgroup.map_commutator,
      ← commutator_def, hcommM]
  have hhat : CFSG.Quasithin.IsHat (↥M₀ ⧸ R.subgroupOf M₀) ↥(alternatingGroup (Fin 6)) :=
    isHat_of_surj (H13.alternatingGroup_nonabelian (by norm_num)) hperfQ φ hφs hφk
  have hO : pCoreOf 2 M₀ = R := pCoreOf_eq_of_surj hRM₀ h.hR2
    (QuotientGroup.mk' (R.subgroupOf M₀)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
    (noNormalTwo_of_isHat hhat (noNormalTwo_of_simple M24.not_isPGroup_alt6))
  have hCR : Subgroup.centralizer (R : Set A) ≤ R := by
    intro x hx
    rw [hmemR]
    refine mem_E_of_cent (hι.mem_heAutGroup x) fun i => ?_
    change ι x * vW5 i = vW5 i * ι x
    obtain ⟨r, -, hr⟩ := hι.exists_of_mem (E_le_heP (vW5_mem_E i))
    have hrR : r ∈ R := by rw [hmemR, hr]; exact vW5_mem_E i
    rw [← hr, ← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx r hrR]
  have hC : M₀ ⊓ Subgroup.centralizer (R : Set A) ≤ R := inf_le_right.trans hCR
  have hEA : IsElemAbelian 2 R := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hι.inj ?_)⟩⟩, fun x hx => hι.inj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact eSub_comm basis_E _ _ ((hmemR a).mp a.2) ((hmemR b).mp b.2)
    · rw [map_pow, map_one, sq]
      exact eSub_sq basis_E _ ((hmemR x).mp hx)
  have hblock := isHatA6Block_of hEA hRM₀ h.hM₀R hO hRc hC h.hper hhat
  have hVR : V = R :=
    (irr_of_hat hEA h.hM₀R hRc hC hhat h.hVR h.hM₀V).resolve_left h.hVne
  have hM₀ : conjClosure M₀ M = M₀ := conjClosure_eq_self' h.hMN
  have hRiso : ↥R ≃* Multiplicative (Fin 6 → ZMod 2) :=
    (MulEquiv.subgroupCongr hR).trans ((((eSub basis_E).comap ι).equivMapOfInjective ι
      hι.inj).trans ((MulEquiv.subgroupCongr (hι.map_comap E_le_heP)).trans (ecoords basis_E)))
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.hSs, ?_⟩))))),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr h.hSs, hblock⟩)))),
    summand_of_card64 (by rw [hVR, hRc])⟩
  rw [hM₀]
  exact ⟨R.subgroupOf M₀, hRn, ⟨(Subgroup.subgroupOfEquivOfLe hRM₀).trans hRiso⟩, hhat⟩

end CFSG.Quasithin.KGC31.He

end
