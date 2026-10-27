module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42IrrDef
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S15
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Tri
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvEdgeCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.S3Vertex
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S41Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace S42B1

omit [Finite G] in
theorem cSecIn_bot_eq (X V : Subgroup G) :
    cSecIn X ⊥ V = X ⊓ Subgroup.centralizer (V : Set G) := by
  unfold cSecIn
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun f hf => Subgroup.mem_inf.mpr ⟨hf.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hf.2 x hx
    rw [Subgroup.mem_bot] at h
    have : f * x = x * f := by
      calc f * x = (f * x * f⁻¹ * x⁻¹) * x * f := by group
        _ = x * f := by rw [h, one_mul]
    exact this.symm
  · intro f hf
    refine Subgroup.subset_closure ⟨hf.1, fun x hx => ?_⟩
    rw [Subgroup.mem_bot]
    have := (Subgroup.mem_centralizer_iff.mp hf.2) x hx
    calc f * x * f⁻¹ * x⁻¹ = (f * x) * f⁻¹ * x⁻¹ := by group
      _ = (x * f) * f⁻¹ * x⁻¹ := by rw [← this]
      _ = 1 := by group

structure Facts (α β : Geo H M) : Prop where
  vα : vtype α = false
  vβ : vtype β = true
  nbr : β ∈ nbrs α
  nle : ¬ Zv α ≤ Qv β
  hcen : stab α ⊓ Subgroup.centralizer (Zv α : Set G) = Qv α
  hVC : Zv α ⊓ Subgroup.centralizer (stab α : Set G) = ⊥
  hgen : ∀ U : Subgroup G, U ≤ Zv α → stab α ≤ Subgroup.normalizer (U : Set G) →
    Zv α ⊓ Subgroup.centralizer ((stab α ⊓ stab β : Subgroup G) : Set G) ≤ U → U = Zv α

section CaseI

variable {α β α₂ α₃ : Geo H M}

theorem exists_dtrans_elem (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    {θ : ↥(stab α) →* Perm (Fin 5)} (hθs : Function.Surjective θ)
    (hθk : ∀ x : ↥(stab α), θ x = 1 ↔ (x : G) ∈ Qv α) (hn : ¬ Zv α₂ ⊓ Qv β ≤ Qv α) :
    ∃ w ∈ Zv α₂ ⊓ Qv β, ∃ hw : w ∈ stab α, θ ⟨w, hw⟩ ≠ 1 ∧ θ ⟨w, hw⟩ ^ 2 = 1 ∧
      Perm.sign (θ ⟨w, hw⟩) = 1 := by
  have hSyl : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA F.nbr
  have hQS : Qv β ≤ stab α ⊓ stab β := by
    have := Qv_le_inf hA T.ha
    rwa [inf_comm] at this
  have hQ₂ : Qv β ≤ stab α₂ := Qv_le_stab_of_mem_nbrs hA T.hb
  have hdec := edge_eq_mul hA F.vβ T.ha F.nle
  have hA₂S : Zv α₂ ⊓ Qv β ≤ stab α ⊓ stab β := inf_le_right.trans hQS
  have hP8 : Nat.card (((stab α ⊓ stab β).subgroupOf (stab α)).map θ) = 8 :=
    card_image_sylow hθs hSyl
  have hNP : ((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ ≤
      ((stab α ⊓ stab β).subgroupOf (stab α)).map θ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hA₂S (Subgroup.mem_subgroupOf.mp hx))
  have hN0 : ((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ ≠ ⊥ := by
    intro hb
    obtain ⟨w₀, hw₀, hw₀Q⟩ := Set.not_subset.mp hn
    have hw₀α : w₀ ∈ stab α := (hA₂S hw₀).1
    have : θ ⟨w₀, hw₀α⟩ ∈ ((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ :=
      ⟨⟨w₀, hw₀α⟩, Subgroup.mem_subgroupOf.mpr hw₀, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact hw₀Q ((hθk _).mp this)
  have hnorm : ((stab α ⊓ stab β).subgroupOf (stab α)).map θ ≤
      Subgroup.normalizer ((((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ : Subgroup (Perm (Fin 5)))
        : Set (Perm (Fin 5))) := by
    have key : ∀ p ∈ ((stab α ⊓ stab β).subgroupOf (stab α)).map θ,
        ∀ x ∈ ((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ,
        p * x * p⁻¹ ∈ ((Zv α₂ ⊓ Qv β).subgroupOf (stab α)).map θ := by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨w', hw', rfl⟩
      have hs' : (s : G) ∈ stab α ⊓ stab β := Subgroup.mem_subgroupOf.mp hs
      have hw'' : (w' : G) ∈ Zv α₂ ⊓ Qv β := Subgroup.mem_subgroupOf.mp hw'
      obtain ⟨q, hq, z, hz, hsqz⟩ := hdec (s : G) ⟨hs'.2, hs'.1⟩
      have hqα : q ∈ stab α := (hQS hq).1
      have hzα : z ∈ stab α := (Zv_le_edge hA T.ha hz).2
      have hsx : s = (⟨q, hqα⟩ : ↥(stab α)) * ⟨z, hzα⟩ := Subtype.ext hsqz
      have hθz : θ ⟨z, hzα⟩ = 1 := (hθk _).mpr (Zv_le_Qv hA α hz)
      refine ⟨⟨q, hqα⟩ * w' * ⟨q, hqα⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact ⟨(Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α₂ (hQ₂ hq)) w').mp
          hw''.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ hq hw''.2) (Subgroup.inv_mem _ hq)⟩
      · rw [hsx, map_mul θ ⟨q, hqα⟩ ⟨z, hzα⟩, hθz, mul_one, map_mul, map_mul, map_inv]
    exact fun p hp => F53B3.O1.mem_normalizer_of_conj (fun x hx => key p hp x hx)
      (fun x hx => by simpa using key p⁻¹ (Subgroup.inv_mem _ hp) x hx)
  obtain ⟨z', hz'N, hz'1, hz'2, hz'sg⟩ :=
    exists_double_transposition_of_normal hP8 hNP hnorm hN0
  obtain ⟨w', hw', rfl⟩ := hz'N
  exact ⟨w', Subgroup.mem_subgroupOf.mp hw', w'.2, hz'1, hz'2, hz'sg⟩

theorem relIndex_Zv_inf_Qv_le (hA : F53Amalgam H M S) (F : Facts α β) :
    (Zv α ⊓ Qv β).relIndex (Zv α) ≤ 2 := by
  have h2 := relIndex_Qv_inf_true hA (nbrs_symm F.nbr) F.vβ
  rw [inf_comm, Subgroup.inf_relIndex_right]
  have hZ : Zv α ≤ stab β ⊓ stab α := Zv_le_edge hA (nbrs_symm F.nbr)
  rw [← h2]
  exact Subgroup.relIndex_le_of_le_right hZ (by rw [h2]; omega)

theorem caseI_index (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃) {w : G}
    (hw : w ∈ Zv α₂ ⊓ Qv β) :
    (Zv α ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Zv α) ≤ 8 := by
  have hv₂ : vtype α₂ = false := vtype_false_of_nbr F.vβ T.hb
  have hQ₂ : Qv β ≤ stab α₂ := Qv_le_stab_of_mem_nbrs hA T.hb
  have hC₁ : (Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂) ≤ Zv α ⊓ Subgroup.centralizer ({w} : Set G) := by
    intro x hx
    refine ⟨hx.1.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hwc := (Zv_le_centerOf_Qv hA α₂ hw.1).2
    exact Subgroup.mem_centralizer_iff.mp hwc x hx.2
  have h1 : (Zv α ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Zv α) ≤
      ((Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂)).relIndex (Zv α) :=
    Subgroup.relIndex_le_of_le_left hC₁ Subgroup.index_ne_zero_of_finite
  have h2 := Subgroup.relIndex_mul_relIndex ((Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂))
    (Zv α ⊓ Qv β) (Zv α) inf_le_left inf_le_left
  have h3 : ((Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂)).relIndex (Zv α ⊓ Qv β) ≤ 4 :=
    relIndex_le_four_of_elemAbelian (quot_stab_five hA hv₂) (inf_le_right.trans hQ₂)
      (F7.isElemAbelian_mono (isElemAbelian_Zv hA α) inf_le_left)
  have h4 := relIndex_Zv_inf_Qv_le hA F
  calc (Zv α ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Zv α)
      ≤ ((Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂)).relIndex (Zv α) := h1
    _ = ((Zv α ⊓ Qv β) ⊓ pCoreOf 2 (stab α₂)).relIndex (Zv α ⊓ Qv β) *
        (Zv α ⊓ Qv β).relIndex (Zv α) := h2.symm
    _ ≤ 4 * 2 := Nat.mul_le_mul h3 h4
    _ = 8 := by norm_num

theorem caseI (hA : F53Amalgam H M S) (hirr : IrrSec) (F : Facts α β) (T : Tri β α α₂ α₃)
    (hn : ¬ Zv α₂ ⊓ Qv β ≤ Qv α) :
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) := by
  obtain ⟨n, θ, hn5, hθs, hθk⟩ := exists_quotHom hA α
  have hn5' : n = 5 := by
    rcases hn5 with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · rw [F.vα] at h; exact absurd h (by decide)
  subst hn5'
  obtain ⟨w, hw, hwα, hθ1, hθ2, hθsg⟩ := exists_dtrans_elem hA F T hθs hθk hn
  have hSyl : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA F.nbr
  have hker : θ.ker = (cSecIn (stab α) ⊥ (Zv α)).subgroupOf (stab α) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, cSecIn_bot_eq, F.hcen]
    exact hθk x
  have hmem : w ∈ oTwoRes (stab α) ⊔ pCoreOf 2 (stab α) := by
    have := (mem_oTwoRes_sup_iff (L := ⊥) (X := Zv α) hθs hker hwα).mpr
      ((Equiv.Perm.mem_alternatingGroup).mpr hθsg)
    rwa [cSecIn_bot_eq, F.hcen] at this
  refine hirr G (stab α) (Zv α) (stab α ⊓ stab β) (quot_stab_five hA F.vα)
    (Zv_le_Qv hA α) (stab_le_normalizer_Zv hA α) (isElemAbelian_Zv hA α) F.hcen
    F.hVC hSyl F.hgen w hmem ?_ (Or.inl ?_) (caseI_index hA F T hw)
  · intro hwQ
    exact hθ1 ((hθk ⟨w, hwα⟩).mpr hwQ)
  · have : θ (⟨w, hwα⟩ ^ 2) = 1 := by rw [map_pow]; exact hθ2
    exact (hθk _).mp this

end CaseI

section CaseII

variable {α β α₂ α₃ : Geo H M}

theorem caseII_eq (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    (hn : Zv α₂ ⊓ Qv β ≤ Qv α) :
    Zv α ⊓ Qv β = Zv α₂ ⊓ Qv β ∧ Zv α₂ ⊓ Qv β = Zv α₃ ⊓ Qv β := by
  have h23 : Zv α₂ ⊓ Qv β = Zv α₃ ⊓ Qv β := by
    obtain ⟨x₁, hx₁, hx₁Q⟩ := Set.not_subset.mp F.nle
    have hxe := Zv_le_edge hA T.ha hx₁
    have hg : ((⟨x₁, stab_le β hxe.1⟩ : ↥(H ⊔ M)) : G) ∈ stab β := hxe.1
    obtain ⟨h2, -⟩ := T.swap hA hg (smul_eq_of_mem_stab hxe.2) hx₁Q
    have hc := conjSub_Aq hg α₂
    rw [h2] at hc
    have hnorm : x₁ ∈ Subgroup.normalizer ((Zv α₂ ⊓ Qv β : Subgroup G) : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hx₁).2 y (hn hy)
    have hc' : conjSub x₁ (Zv α₂ ⊓ Qv β) = Zv α₂ ⊓ Qv β := conjSub_eq_of_mem_normalizer hnorm
    exact hc'.symm.trans hc
  refine ⟨?_, h23⟩
  have T' : Tri β α₃ α α₂ := T.swap₂₃.swap₁₂
  obtain ⟨g, hg, hga, hgQ⟩ := exists_stab_elem hA F.vβ T.hc
  obtain ⟨h1, h2⟩ := T'.swap hA hg hga hgQ
  have := congrArg (conjSub (g : G)) h23
  rw [conjSub_Aq hg α₂, conjSub_Aq hg α₃, h2, hga] at this
  exact this.trans h23.symm

theorem caseII_norm (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    (hn : Zv α₂ ⊓ Qv β ≤ Qv α) :
    stab β ≤ Subgroup.normalizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) := by
  obtain ⟨e1, e2⟩ := caseII_eq hA F T hn
  intro x hx
  refine mem_normalizer_of_conjSub_eq ?_
  have hc := conjSub_Aq (g := ⟨x, stab_le β hx⟩) hx α
  have hmem := smul_mem_nbrs_of_mem_stab (g := ⟨x, stab_le β hx⟩) hx T.ha
  rcases T.all _ hmem with h | h | h
  · rw [h] at hc; exact hc
  · rw [h] at hc; exact hc.trans e1.symm
  · rw [h] at hc; exact hc.trans (e1.trans e2).symm

theorem stab_le_sup_of_Zv_le (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    {K : Subgroup G} (h1 : Zv α ≤ K) (h2 : Zv α₂ ≤ K) : stab β ≤ K ⊔ Qv β := by
  rw [← sup_edges_eq_stab hA F.vβ T.ha T.hb T.hab]
  have e1 := sup_Qv_eq_edge hA F.vβ T.ha (Zv_le_edge hA T.ha) F.nle
  have e2 := sup_Qv_eq_edge hA F.vβ T.hb (Zv_le_edge hA T.hb)
    (not_Zv_le_Qv_of_nbr T.ha T.hb F.nle)
  rw [← e1, ← e2]
  exact sup_le (sup_le_sup_right h1 _) (sup_le_sup_right h2 _)

theorem caseII_false (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    (hn : Zv α₂ ⊓ Qv β ≤ Qv α)
    (hSC : ∀ s ∈ stab α ⊓ stab β,
      s ∈ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) → s ∈ Qv α) : False := by
  have hnorm_A := caseII_norm hA F T hn
  obtain ⟨e1, -⟩ := caseII_eq hA F T hn
  have hQS : Qv β ≤ stab α ⊓ stab β := by
    have := Qv_le_inf hA T.ha
    rwa [inf_comm] at this
  have hQα : Qv α ≤ stab α ⊓ stab β := Qv_le_inf hA F.nbr
  have hQβst : Qv β ≤ stab β := pCoreOf_le 2 _
  have hZc : ∀ z ∈ Zv α, ∀ y ∈ Qv α, y * z = z * y := fun z hz y hy =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 y hy
  have hCn : stab β ≤ Subgroup.normalizer
      ((stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) : Subgroup G) :
        Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (hnorm_A.trans (normalizer_le_normalizer_centralizer _))
  have hNC : Qv α ⊓ Qv β = (stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G)) ⊓
      Qv β := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨hQβst hx.2, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩, hx.2⟩
      exact (hZc a ha.1 x hx.1).symm
    · intro x hx
      exact ⟨hSC x ⟨(hQS hx.2).1, hx.1.1⟩ hx.1.2, hx.2⟩
  have hNn : stab β ≤ Subgroup.normalizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
    rw [hNC]
    exact le_normalizer_inf hCn (le_normalizer_pCoreOf 2 (stab β))
  have hNS : Qv α ⊓ Qv β ≤ stab α ⊓ stab β := fun x hx => hQα hx.1
  have hdec : ∀ q ∈ Qv α, ∃ n ∈ Qv α ⊓ Qv β, ∃ z ∈ Zv α, q = n * z := by
    intro q hq
    obtain ⟨q', hq', z, hz, hqz⟩ := edge_eq_mul hA F.vβ T.ha F.nle q ⟨(hQα hq).2, (hQα hq).1⟩
    refine ⟨q', ⟨?_, hq'⟩, z, hz, hqz⟩
    have : q' = q * z⁻¹ := by rw [hqz]; group
    rw [this]
    exact Subgroup.mul_mem _ hq (Subgroup.inv_mem _ (Zv_le_Qv hA α hz))
  have hK1 : ⁅Qv α, Qv α⁆ ≤ ⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ := by
    refine Subgroup.commutator_le.mpr fun q hq q' hq' => ?_
    obtain ⟨n, hn1, z, hz, rfl⟩ := hdec q hq
    obtain ⟨n', hn1', z', hz', rfl⟩ := hdec q' hq'
    have hzy : ∀ y ∈ Qv α, z * y * z⁻¹ = y := fun y hy => by
      rw [← hZc z hz y hy]; group
    have hzy' : ∀ y ∈ Qv α, z' * y * z'⁻¹ = y := fun y hy => by
      rw [← hZc z' hz' y hy]; group
    have hnQ : n ∈ Qv α := hn1.1
    have hn'Q : n' ∈ Qv α := hn1'.1
    have hz'Q : z' ∈ Qv α := Zv_le_Qv hA α hz'
    have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc n * z * (n' * z') * (n * z)⁻¹ * (n' * z')⁻¹
          = n * (z * (n' * z') * z⁻¹) * n⁻¹ * (z'⁻¹ * n'⁻¹) := by group
        _ = n * (n' * z') * n⁻¹ * (z'⁻¹ * n'⁻¹) := by
          rw [hzy _ (Subgroup.mul_mem _ hn'Q hz'Q)]
        _ = n * n' * (z' * n⁻¹ * z'⁻¹) * n'⁻¹ := by group
        _ = n * n' * n⁻¹ * n'⁻¹ := by rw [hzy' _ (Subgroup.inv_mem _ hnQ)]
    rw [e]
    exact Subgroup.commutator_mem_commutator hn1 hn1'
  have hKeq : ⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ = ⁅Qv α, Qv α⁆ :=
    le_antisymm (Subgroup.commutator_mono inf_le_left inf_le_left) hK1
  have hKb : stab β ≤ Subgroup.normalizer ((⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ : Subgroup G) : Set G) :=
    F53B3.O1.le_normalizer_commutator hNn hNn
  have hKa : stab α ≤ Subgroup.normalizer ((⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ : Subgroup G) : Set G) := by
    rw [hKeq]
    exact F53B3.O1.le_normalizer_commutator (le_normalizer_pCoreOf 2 (stab α))
      (le_normalizer_pCoreOf 2 (stab α))
  have hKS : ⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ ≤ stab α ⊓ stab β := by
    refine Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNS h₁) (hNS h₂))
      (Subgroup.inv_mem _ (hNS h₁))) (Subgroup.inv_mem _ (hNS h₂))
  have hK0 : ⁅Qv α ⊓ Qv β, Qv α ⊓ Qv β⁆ = ⊥ :=
    eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj α β from F.nbr) hKS hKa hKb
  have hQαN : Qv α ⊓ Qv β ≤ Subgroup.centralizer (Qv α : Set G) := by
    intro n hn1
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    obtain ⟨n₁, hn₁, z, hz, rfl⟩ := hdec q hq
    have h1 : n₁ * n = n * n₁ := by
      have := Subgroup.commutator_mem_commutator hn₁ hn1
      rw [hK0, Subgroup.mem_bot, commutatorElement_def] at this
      calc n₁ * n = (n₁ * n * n₁⁻¹ * n⁻¹) * n * n₁ := by group
        _ = n * n₁ := by rw [this, one_mul]
    have h2 : z * n = n * z := (hZc z hz n hn1.1).symm
    calc n₁ * z * n = n₁ * (z * n) := by group
      _ = n₁ * (n * z) := by rw [h2]
      _ = (n₁ * n) * z := by group
      _ = (n * n₁) * z := by rw [h1]
      _ = n * (n₁ * z) := by group
  have hQ₂N : Qv α ⊓ Qv β ≤ Subgroup.centralizer (Qv α₂ : Set G) := by
    obtain ⟨g, hg, hga⟩ := stab_transitive_on_nbrs T.ha T.hb
    have hQ := Qv_smul g α
    rw [hga] at hQ
    rw [hQ]
    exact le_centralizer_conjSub (hNn hg) hQαN
  have hQp : IsPGroup 2 (Qv β) := pCoreOf_isPGroup 2 (stab β)
  have hZ₁ := Zv_le_edge hA T.ha
  have hZ₂ := Zv_le_edge hA T.hb
  have hZC : Zv α ≤ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) := by
    intro z hz
    refine ⟨(hZ₁ hz).1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α hz).2 a (Zv_le_Qv hA α ha.1)
  have hZC₂ : Zv α₂ ≤ stab β ⊓ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) := by
    intro z hz
    refine ⟨(hZ₂ hz).1, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
    have ha' : a ∈ Zv α₂ ⊓ Qv β := e1 ▸ ha
    exact Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA α₂ hz).2 a (Zv_le_Qv hA α₂ ha'.1)
  have hCQ := stab_le_sup_of_Zv_le hA F T hZC hZC₂
  have hK₂n : stab β ≤ Subgroup.normalizer
      ((stab β ⊓ Subgroup.centralizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) : Subgroup G) :
        Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hNn.trans (normalizer_le_normalizer_centralizer _))
  have hZK₁ : Zv α ≤ stab β ⊓ Subgroup.centralizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
    intro z hz
    refine ⟨(hZ₁ hz).1, Subgroup.mem_centralizer_iff.mpr fun n hn1 => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQαN hn1) z (Zv_le_Qv hA α hz)).symm
  have hZK₂ : Zv α₂ ≤ stab β ⊓ Subgroup.centralizer ((Qv α ⊓ Qv β : Subgroup G) : Set G) := by
    intro z hz
    refine ⟨(hZ₂ hz).1, Subgroup.mem_centralizer_iff.mpr fun n hn1 => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp (hQ₂N hn1) z (Zv_le_Qv hA α₂ hz)).symm
  have hKQ := stab_le_sup_of_Zv_le hA F T hZK₁ hZK₂
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d', hd'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(stab β)) 3
    (three_dvd_card_stab hA F.vβ)
  have hdst : (d' : G) ∈ stab β := d'.2
  have hdord : orderOf (d' : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd'
  have hd3 : (d' : G) ^ 3 = 1 := by rw [← hdord]; exact pow_orderOf_eq_one _
  have hdC := mem_of_odd_of_le_sup hCn hQβst hQp hCQ hdst (by decide) hd3
  have hdK := mem_of_odd_of_le_sup hK₂n hQβst hQp hKQ hdst (by decide) hd3
  have hcomm : ∀ x ∈ Qv β, (d' : G) * x * (d' : G)⁻¹ * x⁻¹ ∈ Qv α ⊓ Qv β := by
    intro x hx
    rw [hNC]
    refine ⟨?_, ?_⟩
    · have e : (d' : G) * x * (d' : G)⁻¹ * x⁻¹ = (d' : G) * (x * (d' : G)⁻¹ * x⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hdC
        ((Subgroup.mem_normalizer_iff.mp (hCn (hQβst hx)) _).mp (Subgroup.inv_mem _ hdC))
    · exact Subgroup.mul_mem _
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab β) hdst) x).mp hx)
        (Subgroup.inv_mem _ hx)
  have hdN : ∀ n ∈ Qv α ⊓ Qv β, (d' : G) * n * (d' : G)⁻¹ = n := by
    intro n hn1
    have := Subgroup.mem_centralizer_iff.mp hdK.2 n hn1
    calc (d' : G) * n * (d' : G)⁻¹ = n * d' * (d' : G)⁻¹ := by rw [this]
      _ = n := by group
  have hcen := centralizes_of_comm_mod hQp inf_le_right (by decide) hd3 hdN hcomm
  have hdQ : (d' : G) ∈ Qv β := by
    refine charTwo_stab hA β ⟨hdst, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hcen x hx
    calc x * (d' : G) = ((d' : G) * x * (d' : G)⁻¹) * d' := by rw [this]
      _ = d' * x := by group
  have h1 := eq_one_of_pow_odd_of_isPGroup hQp hdQ (by decide) hd3
  rw [h1, orderOf_one] at hdord
  omega

theorem caseII (hA : F53Amalgam H M S) (F : Facts α β) (T : Tri β α α₂ α₃)
    (hn : Zv α₂ ⊓ Qv β ≤ Qv α) :
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) := by
  by_cases hd : ∃ s ∈ stab α ⊓ stab β,
      s ∈ Subgroup.centralizer ((Zv α ⊓ Qv β : Subgroup G) : Set G) ∧ s ∉ Qv α
  · obtain ⟨s, hs, hsC, hsQ⟩ := hd
    have hsX : s ∈ stab α := hs.1
    have hle : Zv α ⊓ Qv β ≤ Zv α ⊓ Subgroup.centralizer ({s} : Set G) := fun x hx =>
      ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsC x hx)⟩
    have h1 : (Zv α ⊓ Subgroup.centralizer ({s} : Set G)).relIndex (Zv α) ≤ 2 :=
      (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans
        (relIndex_Zv_inf_Qv_le hA F)
    have h2 : (Zv α ⊓ Subgroup.centralizer ({s} : Set G)).relIndex (Zv α) ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      apply hsQ
      rw [← F.hcen]
      exact ⟨hsX, Subgroup.mem_centralizer_iff.mpr fun v hv =>
        Subgroup.mem_centralizer_singleton_iff.mp (h hv).2⟩
    have h3 : (Zv α ⊓ Subgroup.centralizer ({s} : Set G)).relIndex (Zv α) ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have h4 : (Zv α ⊓ Subgroup.centralizer ({s} : Set G)).relIndex (Zv α) = 2 := by omega
    left
    have := hss15 G (stab α) (Zv α) (quot_stab_five hA F.vα) (Zv_le_Qv hA α)
      (stab_le_normalizer_Zv hA α) (isElemAbelian_Zv hA α) F.hcen s hsX h4
    rwa [F.hVC] at this
  · push Not at hd
    exact (caseII_false hA F T hn fun s hs hsC => hd s hs hsC).elim

end CaseII

end S42B1

open S42B1

theorem hss42Comm_b_one (hA : F53Amalgam H M S) (hirr : IrrSec) {α β α' : Geo H M}
    (hc : IsCritData α β α') (hα : vtype α = false)
    (hz : ⁅Zv α, Zv α'⁆ = ⊥) (hb : bMin H M = 1) :
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α) := by
  have hZβc : Zv β ≤ centerOf (stab β) := Zv_central_of_comm_eq_bot hA hc hz
  have hαβ : β = α' := by
    have h := hc.dist_eq'
    rw [hb] at h
    exact (CosetGeom.dist_eq_zero_iff hA.amalgam.gen).mp (by omega)
  subst hαβ
  have hβn : β ∈ nbrs α := hc.adj
  have hαn : α ∈ nbrs β := hc.adj.symm
  have hvβ : vtype β = true := by
    cases h : vtype β
    · exact absurd (hα.trans h.symm) (vtype_ne_of_adj hc.adj)
    · rfl
  have hTs : IsSylowTwoOf (stab α ⊓ stab β) (stab α) := sylow_stab_inf_left hA hβn
  have hcent := EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_inf_centralizer_edge_eq hA hc.adj
    hZβc
  have hZβ : Zv β = quasithinOmegaOneCenter (stab α ⊓ stab β) := by
    rw [inf_comm]; exact (Zv_eq_omegaOneCenter_inf hA hαn hZβc).1
  have hcen0 : centerOf (stab α) = ⊥ := centerOf_eq_bot_of_Zv_central hA hαn hZβc
  have hF : Facts α β :=
    { vα := hα
      vβ := hvβ
      nbr := hβn
      nle := hc.not_le
      hcen := centralizer_Zv_eq_Qv_of_bAt hA hc.bAt_eq
      hVC := by
        rw [eq_bot_iff, ← hcen0]
        exact fun x hx => ⟨pCoreOf_le 2 _ (Zv_le_Qv hA α hx.1), hx.2⟩
      hgen := by
        intro U hUV hUn hle
        refine le_antisymm hUV ?_
        have hβK : Zv β ≤ U := hcent ▸ hle
        rw [Zv_eq_conjClosure hTs, ← hZβ]
        refine (Subgroup.closure_le U).mpr ?_
        rintro _ ⟨g, hg, z, hz', rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hUn hg) z).mp (hβK hz') }
  obtain ⟨α₂, α₃, T⟩ := exists_tri hA hvβ hαn
  by_cases hn : Zv α₂ ⊓ Qv β ≤ Qv α
  · exact caseII hA hF T hn
  · exact caseI hA hirr hF T hn

end F53.Stellmacher

end CFSG.Quasithin
