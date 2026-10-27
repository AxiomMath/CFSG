module

public import CFSG.Quasithin.Background.Harris.R1.Q8D
public import CFSG.Quasithin.Background.Harris.R1.Q8Aux
public import CFSG.Quasithin.Background.Harris.R1.Q8Ker
public import CFSG.Quasithin.Background.Harris.R1.QbetaN2

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SzR1
  CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}

@[expose] def PermSevenAt (Ω : Type) [Fintype Ω] (pt : Ω) : Prop :=
  ∀ c y : Equiv.Perm Ω, orderOf c = 7 → c pt = pt → (∃ n : ℕ, y ^ 2 ^ n = 1) →
    y * c = c * y → y pt = pt → y = 1

theorem D_le_Z_odd [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)
    (hΩ : 4 ≤ Fintype.card Ω) (hodd : Odd (Fintype.card Ω)) {i₀ j₀ : Ω} (hij : i₀ ≠ j₀)
    (hcen : ∀ x ∈ vBeta K1 L2 S Zs, (∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) → x ∈ Zs)
    (hZS : ∀ u ∈ S, (∀ s ∈ S, u * s = s * u) → u * u = 1 → u ∈ Zs)
    (hker : ∀ k : ↥K1, C.D.act k = 1 → (k : G) ∈ pCoreOf 2 K1)
    (hs : IsSimpleGroup (OTwoQuot K1)) {t : G} (htK : t ∈ K1) (htB : t ∈ borelOf K1 S)
    (ht7 : orderOf t = 7) (hP7 : PermSevenAt Ω C.D.pt) :
    C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) ≤ Zs := by
  classical
  have hkS : C.kerM ≤ S := kerM_le_S C hker
  have hMeq : C.kerM ⊓ S = C.kerM := inf_eq_left.mpr hkS
  obtain ⟨g, y, z, h, -⟩ := qd_of_famCtx_gen C hΩ hodd hij Finset.univ.toList
    (Finset.nodup_toList _) (by simp) hcen hZS
  have hSM : S ≤ Subgroup.normalizer ((C.kerM ⊓ S : Subgroup G) : Set G) :=
    F7.le_normalizer_inf (le_sup_right.trans C.sup_le_normalizer_kerM) Subgroup.le_normalizer
  have hS2 : IsPGroup 2 S := h.hS2
  have hQS : pCoreOf 2 (L2 ⊔ S) ≤ S := h.vh.qs
  have hEQ := h.conjSub_D_le_Q
  have hES : conjSub g (C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G)) ≤ S :=
    hEQ.trans hQS
  have hcomm := h.commute_D_conjSub hSM
  have hK1D : K1 ≤ Subgroup.normalizer
      ((C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) : Subgroup G) : Set G) := by
    rw [hMeq]
    refine F7.le_normalizer_inf (le_sup_left.trans C.sup_le_normalizer_kerM) (fun k hk => ?_)
    have hWc : conjSub k (vBeta K1 L2 S Zs) = vBeta K1 L2 S Zs :=
      F7.conjSub_eq_of_mem_normalizer
        (le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) (Subgroup.mem_sup_left hk))
    apply Vert.mem_normalizer_of_conjSub_eq
    rw [← conjSub_centralizer, hWc]
  have hKSD : K1 ⊔ S ≤ Subgroup.normalizer
      ((C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) : Subgroup G) : Set G) :=
    sup_le hK1D h.hDS
  set D : Subgroup G := C.kerM ⊓ S ⊓ Subgroup.centralizer (vBeta K1 L2 S Zs : Set G) with hD
  set Cn : Subgroup G := (K1 ⊔ S) ⊓ Subgroup.centralizer (D : Set G) with hCn
  have hEC : conjSub g D ≤ Cn := fun e he =>
    ⟨Subgroup.mem_sup_right (hES he), Subgroup.mem_centralizer_iff.mpr
      (fun d hd => hcomm d hd e he)⟩
  have hCnN : K1 ⊔ S ≤ Subgroup.normalizer (Cn : Set G) := by
    refine F7.le_normalizer_inf Subgroup.le_normalizer (fun x hx => ?_)
    apply Vert.mem_normalizer_of_conjSub_eq
    rw [← conjSub_centralizer, conjSub_eq_of_mem_normalizer (hKSD hx)]
  set X : Subgroup G := K1 ⊓ (Cn ⊔ C.kerM) with hX
  have hKX : K1 ≤ Subgroup.normalizer ((Cn ⊔ C.kerM : Subgroup G) : Set G) :=
    le_normalizer_sup_aux (le_sup_left.trans hCnN) (le_sup_left.trans C.sup_le_normalizer_kerM)
  have hXn : ∀ k ∈ K1, ∀ x ∈ X, k * x * k⁻¹ ∈ X := by
    intro k hk x hx
    refine ⟨K1.mul_mem (K1.mul_mem hk hx.1) (K1.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKX hk) x).mp hx.2
  have hQX : pCoreOf 2 K1 ≤ X := fun q hq =>
    ⟨pCoreOf_le 2 K1 hq, Subgroup.mem_sup_right (pCoreK1_le_kerM C hodd hq)⟩
  have hmain : conjSub g D ≤ C.kerM := by
    rcases normal_eq_pCore_or_top hs inf_le_left hXn hQX with hXe | hXe
    ·
      intro e he
      have heS : e ∈ S := hES he
      have heKS : e ∈ K1 ⊔ S := Subgroup.mem_sup_right heS
      have hN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) :=
        sup_le Subgroup.le_normalizer C.hSK
      have hcomm' : ∀ k : ↥K1,
          permHom C ⟨e, heKS⟩ * C.D.act k = C.D.act k * permHom C ⟨e, heKS⟩ := by
        intro k
        have hkH : (k : G) ∈ K1 ⊔ S := Subgroup.mem_sup_left k.2
        have hcK : e * k * e⁻¹ * (k : G)⁻¹ ∈ K1 :=
          K1.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN heKS) k).mp k.2) (K1.inv_mem k.2)
        have hcC : e * k * e⁻¹ * (k : G)⁻¹ ∈ Cn := by
          have h1 : (k : G) * e⁻¹ * (k : G)⁻¹ ∈ Cn :=
            (Subgroup.mem_normalizer_iff.mp (hCnN hkH) e⁻¹).mp (Cn.inv_mem (hEC he))
          have e1 : e * k * e⁻¹ * (k : G)⁻¹ = e * ((k : G) * e⁻¹ * (k : G)⁻¹) := by group
          rw [e1]
          exact Cn.mul_mem (hEC he) h1
        have hcX : e * k * e⁻¹ * (k : G)⁻¹ ∈ pCoreOf 2 K1 := by
          rw [← hXe]
          exact ⟨hcK, Subgroup.mem_sup_left hcC⟩
        have hcO : e * k * e⁻¹ * (k : G)⁻¹ ∈ C.kerM := pCoreK1_le_kerM C hodd hcX
        have hcH : e * k * e⁻¹ * (k : G)⁻¹ ∈ K1 ⊔ S := Subgroup.mem_sup_left hcK
        have h1 := (permHom_eq_one_iff C ⟨_, hcH⟩).2 hcO
        have e2 : (⟨e * k * e⁻¹ * (k : G)⁻¹, hcH⟩ : ↥(K1 ⊔ S)) =
            ⟨e, heKS⟩ * ⟨(k : G), hkH⟩ * ⟨e, heKS⟩⁻¹ * ⟨(k : G), hkH⟩⁻¹ := rfl
        rw [e2, map_mul, map_mul, map_mul, map_inv, map_inv, permHom_K1] at h1
        exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
      exact (permHom_eq_one_iff C ⟨e, heKS⟩).mp (perm_eq_one_of_commute C hΩ _ hcomm')
    ·
      have htX : t ∈ X := hXe htK
      obtain ⟨c, hcC, m, hmM, htcm⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
        (show C.kerM ≤ Subgroup.normalizer (Cn : Set G) from C.kerM_le_sup.trans hCnN)).mp htX.2
      have ht7' : t ^ 7 = 1 := by
        have := pow_orderOf_eq_one t
        rwa [ht7] at this
      obtain ⟨k₂, hk₂⟩ := hS2 ⟨m, hkS hmM⟩
      have hm2 : m ^ 2 ^ k₂ = 1 := by
        have := congrArg Subtype.val hk₂
        simpa using this
      have huE : ∀ d ∈ D, m * d * m⁻¹ ∈ D := fun d hd =>
        (Subgroup.mem_normalizer_iff.mp (h.hDS (hkS hmM)) d).mp hd
      have htD : ∀ d ∈ D, t * d * t⁻¹ = d := by
        refine centralizes_of_conj_eq (n := 7) (k := k₂) (by decide) ht7' hm2 huE ?_
        intro d hd
        rw [htcm]
        have h1 := Subgroup.mem_centralizer_iff.mp hcC.2 (m * d * m⁻¹) (huE d hd)
        calc c * m * d * (c * m)⁻¹ = c * (m * d * m⁻¹) * c⁻¹ := by group
          _ = m * d * m⁻¹ := by rw [← h1]; group
      have hSL2 : S ≤ Subgroup.normalizer (L2 : Set G) := C.h.hyp.h2.normalizes
      have htN2 : t ∈ Subgroup.normalizer (L2 : Set G) := C.h.hyp.h2.borel_le htB
      obtain ⟨l, hl, s, hs', hgls⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes hSL2).mp h.hg
      have hr := commutator_mem_pCoreOf_of_pow_seven C.h.s3 htN2 ht7' hl
      have hHN : L2 ⊔ S ≤ Subgroup.normalizer ((pCoreOf 2 L2 : Subgroup G) : Set G) :=
        sup_le (le_normalizer_pCoreOf 2 L2) (le_normalizer_pCoreOf_of_le_normalizer hSL2)
      have hpcQ : pCoreOf 2 L2 ≤ pCoreOf 2 (L2 ⊔ S) :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((pCoreOf_le 2 L2).trans le_sup_left) hHN (pCoreOf_isPGroup 2 L2)
      have hrQ := hpcQ hr
      obtain ⟨k₃, hk₃⟩ := pCoreOf_isPGroup 2 L2 ⟨_, hr⟩
      have hr2 : (t * l * t⁻¹ * l⁻¹) ^ 2 ^ k₃ = 1 := by
        have := congrArg Subtype.val hk₃
        simpa using this
      have hrE : ∀ e ∈ conjSub g D, (t * l * t⁻¹ * l⁻¹) * e * (t * l * t⁻¹ * l⁻¹)⁻¹ ∈ conjSub g D :=
        fun e he => (Subgroup.mem_normalizer_iff.mp (h.Q_le_normalizer_conjSub hrQ) e).mp he
      have htE : ∀ e ∈ conjSub g D, t * e * t⁻¹ = e := by
        refine centralizes_of_conj_eq (n := 7) (k := k₃) (by decide) ht7' hr2 hrE ?_
        intro e he
        have hd := mem_conjSub.mp he
        have hd' : s * (g⁻¹ * e * g) * s⁻¹ ∈ D :=
          (Subgroup.mem_normalizer_iff.mp (h.hDS hs') _).mp hd
        have htd := htD _ hd'
        have eg : e = l * (s * (g⁻¹ * e * g) * s⁻¹) * l⁻¹ := by
          have : g⁻¹ = s⁻¹ * l⁻¹ := by rw [hgls]; group
          rw [this, hgls]; group
        set d' := s * (g⁻¹ * e * g) * s⁻¹ with hd'def
        have e1 : t * d' = d' * t := by
          calc t * d' = (t * d' * t⁻¹) * t := by group
            _ = d' * t := by rw [htd]
        calc t * e * t⁻¹ = t * (l * d' * l⁻¹) * t⁻¹ := by rw [← eg]
          _ = (t * l * t⁻¹ * l⁻¹) * l * (t * d' * t⁻¹) * l⁻¹ * (t * l * t⁻¹ * l⁻¹)⁻¹ := by group
          _ = (t * l * t⁻¹ * l⁻¹) * (l * d' * l⁻¹) * (t * l * t⁻¹ * l⁻¹)⁻¹ := by rw [htd]; group
          _ = (t * l * t⁻¹ * l⁻¹) * e * (t * l * t⁻¹ * l⁻¹)⁻¹ := by rw [← eg]
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hc7 : orderOf (C.D.act ⟨t, htK⟩) = 7 := by
        have hpow : (C.D.act ⟨t, htK⟩) ^ 7 = 1 := by
          rw [← map_pow]
          have : (⟨t, htK⟩ : ↥K1) ^ 7 = 1 := Subtype.ext (by simpa using ht7')
          rw [this, map_one]
        have hne : C.D.act ⟨t, htK⟩ ≠ 1 := by
          intro h1
          have h2 := hker ⟨t, htK⟩ h1
          obtain ⟨k₄, hk₄⟩ := pCoreOf_isPGroup 2 K1 ⟨t, h2⟩
          have h3 : t ^ 2 ^ k₄ = 1 := by
            have := congrArg Subtype.val hk₄
            simpa using this
          have h4 : 7 ∣ 2 ^ k₄ := ht7 ▸ orderOf_dvd_of_pow_eq_one h3
          have h5 := (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4)
          omega
        exact orderOf_eq_prime hpow hne
      have hcpt : C.D.act ⟨t, htK⟩ C.D.pt = C.D.pt := (C.D.stab _).mpr htB
      intro e he
      have heS : e ∈ S := hES he
      have heKS : e ∈ K1 ⊔ S := Subgroup.mem_sup_right heS
      refine (permHom_eq_one_iff C ⟨e, heKS⟩).mp (hP7 _ _ hc7 hcpt ?_ ?_ ?_)
      · obtain ⟨n, hn⟩ := hS2 ⟨e, heS⟩
        refine ⟨n, ?_⟩
        have h1 : (⟨e, heKS⟩ : ↥(K1 ⊔ S)) ^ 2 ^ n = 1 := Subtype.ext (by
          have := congrArg Subtype.val hn
          simpa using this)
        rw [← map_pow, h1, map_one]
      · rw [← permHom_K1 C ⟨t, htK⟩, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show e * t = t * e
        have := htE e he
        calc e * t = (t * e * t⁻¹) * t := by rw [this]
          _ = t * e := by group
      · show permOf C ⟨e, heKS⟩ C.D.pt = C.D.pt
        exact permOf_eq_of_conjSub C (by
          rw [C.Vf_pt]
          exact conjSub_eq_of_mem_normalizer (C.hSV heS))
  have hEM : conjSub g D ≤ C.kerM ⊓ S := le_inf hmain hES
  exact h.D_le_Z_of_conjSub_le hSM hEM

end CFSG.Quasithin.Background.Harris.R1
