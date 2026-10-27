module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135MS
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.C135.N1

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q map_eq_one_of_mem_centralizer
  exists_smul_of_commute mem_normalizer_centralizer_of_mem mem_pCoreOf_iff')
open CFSG.Quasithin.H13.Ch4.C135 (crd crd_mul crd_one crd_injective crd_surjective crd_conj_false
  cnj coe_cnj cnj_one cnj_mul le_normalizer_centerOf msPair_facts slNat slNat_surjective
  slNat_eq_one_iff moduleAct_true_eq dualHom dualHom_dualHom)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Cent

variable {X L : Subgroup G} {F : Type} [Field F] {α : ↥L →* ↥(StatedSL 3 F)}

theorem burnsideC135_centralizer_U_le' {R : Subgroup G} (hMS : IsMSPair X R)
    (hG : (X : Set G) = (L : Set G) * (R : Set G)) (hα : IsModO2Surj L α) (hLX : L ≤ X)
    (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hU : IsSumOfNaturalModulesVia L (centerOf (c134Q X L)) ⊥ α false 1) :
    X ⊓ Subgroup.centralizer (centerOf (c134Q X L) : Set G) ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hRG, -, hR2⟩ := msPair_facts hMS
  set Y := X ⊓ Subgroup.centralizer (centerOf (c134Q X L) : Set G) with hY
  have hXU : X ≤ Subgroup.normalizer (centerOf (c134Q X L) : Set G) :=
    le_normalizer_centerOf (le_normalizer_c134Q hXL)
  have hGY : X ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (mem_normalizer_centralizer_of_mem (hXU hg))
  have hLN : (L.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLX]
    exact hXL
  set φ := QuotientGroup.mk' (L.subgroupOf X) with hφ
  have hsurj : Function.Surjective (φ.comp (Subgroup.inclusion hRG)) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf X) z
    have hg : (g : G) ∈ (L : Set G) * (R : Set G) := by rw [← hG]; exact g.2
    obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hg
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    show ((Subgroup.inclusion hRG ⟨r, hr⟩)⁻¹ * g : ↥X).1 ∈ L
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
    rw [← hlr]
    have h1 := (Subgroup.mem_normalizer_iff.mp (hXL (hRG (R.inv_mem hr))) l).mp hl
    simpa [mul_assoc] using h1
  have hQ2 : IsPGroup 2 (↥X ⧸ L.subgroupOf X) := hR2.of_surjective _ hsurj
  have hY2 : IsPGroup 2 Y := by
    rintro ⟨y, hyG, hyC⟩
    obtain ⟨k, hk⟩ := hQ2 (φ ⟨y, hyG⟩)
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hk
    have hyk : y ^ 2 ^ k ∈ L := hk
    have hyC' : y ^ 2 ^ k ∈ Subgroup.centralizer (centerOf (c134Q X L) : Set G) :=
      Subgroup.pow_mem _ hyC _
    have h1 : α ⟨_, hyk⟩ = 1 := map_eq_one_of_mem_centralizer hU one_ne_zero hyC'
    have h2 : (⟨_, hyk⟩ : ↥L) ∈ α.ker := h1
    rw [hα.2] at h2
    obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup ⟨_, h2⟩
    refine ⟨k + m, Subtype.ext ?_⟩
    have h3 := congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
    rw [pow_add, pow_mul]
    exact h3
  exact le_pCoreOf_of_le_normalizer 2 inf_le_left hGY hY2

theorem burnsideC135_commute_U [CharP F 2] {Q : Subgroup G} (hα : IsModO2Surj L α)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hU : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1) {t u : G}
    (htN : t ∈ Subgroup.normalizer (centerOf Q : Set G))
    (htL : ∀ g ∈ L, t * g * t⁻¹ * g⁻¹ ∈ Q) {m : ℕ} (htm : t ^ 2 ^ m = 1)
    (hu : u ∈ centerOf Q) : t * u = u * t := by
  classical
  set U := centerOf Q with hUdef
  have hGU : L ≤ Subgroup.normalizer (U : Set G) := le_normalizer_centerOf hLQ
  let eq : ↥U ≃ (Fin 1 → Fin 3 → F) := Equiv.ofBijective (crd hU) ⟨crd_injective hU,
    crd_surjective hU⟩
  have heq : ∀ v, eq v = crd hU v := fun v => rfl
  have hcrd1 : ∀ v : ↥U, crd hU v = fun _ => crd hU v 0 := fun v => by
    funext i
    rw [Subsingleton.elim i 0]
  let elt : (Fin 3 → F) → ↥U := fun x => eq.symm (fun _ => x)
  have hcrd_elt : ∀ x, crd hU (elt x) 0 = x := fun x => by
    rw [← heq, Equiv.apply_symm_apply]
  have helt_crd : ∀ v : ↥U, elt (crd hU v 0) = v := fun v => by
    apply eq.injective
    rw [Equiv.apply_symm_apply, heq, ← hcrd1]
  have helt_add : ∀ x y, elt (x + y) = elt x * elt y := fun x y => by
    apply eq.injective
    rw [Equiv.apply_symm_apply, heq, crd_mul, ← heq, ← heq, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    rfl
  have hconjL : ∀ (g : ↥L) (v : ↥U), crd hU (cnj (hGU g.2) v) 0 =
      ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        crd hU v 0 := by
    intro g v
    rw [crd_conj_false hU g v _ rfl]
    rfl
  have hcomm : ∀ (g : ↥L) (v : ↥U), cnj htN (cnj (hGU g.2) v) =
      cnj (hGU g.2) (cnj htN v) := by
    intro g v
    apply Subtype.ext
    simp only [coe_cnj]
    have hc : t * (g : G) * t⁻¹ * (g : G)⁻¹ ∈ Q := htL g g.2
    have hw : (g : G) * (t * v * t⁻¹) * (g : G)⁻¹ ∈ U :=
      (cnj (hGU g.2) (cnj htN v)).2
    have h1 := Subgroup.mem_centralizer_iff.mp hw.2 _ hc
    calc t * (↑g * ↑v * (↑g)⁻¹) * t⁻¹ =
          (t * ↑g * t⁻¹ * (↑g)⁻¹) * (↑g * (t * ↑v * t⁻¹) * (↑g)⁻¹) *
            (t * ↑g * t⁻¹ * (↑g)⁻¹)⁻¹ := by group
      _ = ↑g * (t * ↑v * t⁻¹) * (↑g)⁻¹ := by rw [h1]; group
  let φ : (Fin 3 → F) →+ (Fin 3 → F) :=
    { toFun := fun x => crd hU (cnj htN (elt x)) 0
      map_zero' := by
        have h0 : elt 0 = 1 := by
          rw [← helt_crd 1, crd_one]
          rfl
        rw [h0, cnj_one, crd_one]
        rfl
      map_add' := fun x y => by
        rw [helt_add, cnj_mul, crd_mul]
        rfl }
  have hφ : ∀ x, φ x = crd hU (cnj htN (elt x)) 0 := fun x => rfl
  obtain ⟨c, hc⟩ := exists_smul_of_commute φ (by
    intro i j hij b x
    obtain ⟨g, hg⟩ := slNat_surjective hα.1 (Matrix.SpecialLinearGroup.transvection hij b)
    have he : elt ((Matrix.SpecialLinearGroup.transvection hij b :
        Matrix (Fin 3) (Fin 3) F) *ᵥ x) = cnj (hGU g.2) (elt x) := by
      rw [← helt_crd (cnj _ (elt x)), hconjL, hcrd_elt, hg]
    rw [hφ, hφ, he, hcomm, hconjL, hg])
  have hsc : ∀ v : ↥U, crd hU (cnj htN v) 0 = c • crd hU v 0 := fun v => by
    have := hc (crd hU v 0)
    rw [hφ, helt_crd] at this
    exact this
  have hpow : ∀ (k : ℕ) (v : ↥U),
      crd hU (cnj (Subgroup.pow_mem _ htN k) v) 0 = c ^ k • crd hU v 0 := by
    intro k
    induction k with
    | zero =>
      intro v
      have h1 : cnj (Subgroup.pow_mem _ htN 0) v = v := Subtype.ext (by simp [coe_cnj])
      rw [h1, pow_zero, one_smul]
    | succ k ih =>
      intro v
      have h1 : cnj (Subgroup.pow_mem _ htN (k + 1)) v =
          cnj htN (cnj (Subgroup.pow_mem _ htN k) v) :=
        Subtype.ext (by simp only [coe_cnj]; rw [pow_succ']; group)
      rw [h1, hsc, ih, smul_smul, pow_succ']
  have hcm : c ^ 2 ^ m = 1 := by
    have h1 := hpow (2 ^ m) (elt (Pi.single 0 1))
    have h2 : cnj (Subgroup.pow_mem _ htN (2 ^ m)) (elt (Pi.single 0 1)) = elt (Pi.single 0 1) :=
      Subtype.ext (by simp [coe_cnj, htm])
    rw [h2, hcrd_elt] at h1
    have h3 := congrFun h1 0
    simp at h3
    exact h3.symm
  have hc1 : c = 1 := by
    have h1 : (c - 1) ^ 2 ^ m = 0 := by rw [sub_pow_char_pow, hcm, one_pow, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h1)
  have h1 : cnj htN ⟨u, hu⟩ = ⟨u, hu⟩ := by
    apply crd_injective hU
    rw [hcrd1 (cnj htN _), hcrd1 ⟨u, hu⟩, hsc, hc1, one_smul]
  have h2 : t * u * t⁻¹ = u := congrArg Subtype.val h1
  calc t * u = t * u * t⁻¹ * t := by group
    _ = u * t := by rw [h2]

theorem burnsideC135_comm_L_of_triv {Q : Subgroup G} (hα : IsModO2Surj L α)
    (h2 : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2) {t : G}
    (htL : t ∈ Subgroup.normalizer (L : Set G)) (htQ : t ∈ Subgroup.normalizer (Q : Set G))
    (htriv : ∀ q ∈ Q, t * q * t⁻¹ * q⁻¹ ∈ centerOf Q) :
    ∀ g ∈ L, t * g * t⁻¹ * g⁻¹ ∈ pCoreOf 2 L := by
  classical
  intro g hg
  have hm : t * g * t⁻¹ * g⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp htL g).mp hg) (L.inv_mem hg)
  set m : ↥L := ⟨_, hm⟩ with hmdef
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := h2.1
  have hmq : ∀ q ∈ Q, (m : G) * q * (m : G)⁻¹ * q⁻¹ ∈ centerOf Q := by
    intro q hq
    have hUn : Q ≤ Subgroup.normalizer (centerOf Q : Set G) :=
      le_normalizer_centerOf (fun x hx => Subgroup.le_normalizer hx)
    have hXU : t ∈ Subgroup.normalizer (centerOf Q : Set G) :=
      le_normalizer_centerOf (fun x hx => hx) htQ
    have hgU : g ∈ Subgroup.normalizer (centerOf Q : Set G) :=
      le_normalizer_centerOf hLQ hg
    have hq' : g⁻¹ * q * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hg)) q).mp hq
      simpa [mul_assoc] using this
    have hq'inv : (g⁻¹ * q * g)⁻¹ ∈ Q := Q.inv_mem hq'
    set q' := g⁻¹ * q * g with hq'def
    have hu₁U : q'⁻¹ * (t⁻¹ * q' * t) ∈ centerOf Q := by
      have h1 := htriv _ hq'inv
      have hXU' : t⁻¹ ∈ Subgroup.normalizer (centerOf Q : Set G) :=
        (Subgroup.normalizer (centerOf Q : Set G)).inv_mem hXU
      have h2 := (Subgroup.mem_normalizer_iff.mp hXU' _).mp h1
      have e : t⁻¹ * (t * q'⁻¹ * t⁻¹ * q'⁻¹⁻¹) * t⁻¹⁻¹ = q'⁻¹ * (t⁻¹ * q' * t) := by group
      rw [e] at h2
      exact h2
    set u₁ := q'⁻¹ * (t⁻¹ * q' * t) with hu₁
    set u₂ := g * u₁ * g⁻¹ with hu₂
    have hu₂U : u₂ ∈ centerOf Q := (Subgroup.mem_normalizer_iff.mp hgU u₁).mp hu₁U
    set u₃ := t * u₂ * t⁻¹ with hu₃
    have hu₃U : u₃ ∈ centerOf Q := (Subgroup.mem_normalizer_iff.mp hXU u₂).mp hu₂U
    have hqU : t * q * t⁻¹ * q⁻¹ ∈ centerOf Q := htriv q hq
    have key : (m : G) * q * (m : G)⁻¹ * q⁻¹ = (t * q * t⁻¹ * q⁻¹) * (q * u₃ * q⁻¹) := by
      rw [hmdef, hu₃, hu₂, hu₁, hq'def]
      group
    rw [key]
    refine (centerOf Q).mul_mem hqU ?_
    exact (Subgroup.mem_normalizer_iff.mp (hUn hq) u₃).mp hu₃U
  obtain ⟨hLQ', -, β, hβs, hβk, hβeq⟩ := h2
  have hfix : ∀ v : Fin 3 → F, ((dualHom (slNat α m) : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    obtain ⟨q, hq⟩ := hβs (Multiplicative.ofAdd (fun _ => v))
    have hmem : (m : G) * q * (m : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ' m.2) _).mp q.2
    have h1 := hβeq m q ⟨_, hmem⟩ rfl 0
    rw [moduleAct_true_eq] at h1
    have h3 : β ⟨_, hmem⟩ = β q := by
      have h4 : (q⁻¹ * ⟨_, hmem⟩ : ↥Q) ∈ β.ker := by
        rw [hβk, Subgroup.mem_subgroupOf]
        have h5 := hmq q q.2
        have h6 : ((q⁻¹ * ⟨_, hmem⟩ : ↥Q) : G) =
            (q : G)⁻¹ * ((m : G) * q * (m : G)⁻¹ * (q : G)⁻¹) * q := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [h6]
        have h7 := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_centerOf (fun x hx => Subgroup.le_normalizer hx)
            (Q.inv_mem q.2)) _).mp h5
        rwa [inv_inv] at h7
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h4
      exact h4.symm
    rw [h3, hq] at h1
    exact h1.symm
  have hd1 : dualHom (slNat α m) = 1 := burnsideC135_eq_one_of_dact fun v => by
    funext i
    exact hfix (v i)
  have hs1 : slNat α m = 1 := by
    rw [← dualHom_dualHom (slNat α m), hd1, map_one]
  have hα1 : α m = 1 := (slNat_eq_one_iff m).mp hs1
  have h2' : m ∈ α.ker := hα1
  rw [hα.2] at h2'
  exact (mem_pCoreOf_iff' m).mpr h2'

end Cent

end CFSG.ASVolI

end
