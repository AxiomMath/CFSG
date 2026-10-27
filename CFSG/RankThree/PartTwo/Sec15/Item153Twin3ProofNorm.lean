module

public import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofNorm
public import CFSG.RankThree.PartTwo.Sec15.Item153Twin3ProofCase7
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofPGL
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof153Twin3

open Proof153Twin2

section Triple

variable {T : Type*} [Group T]

theorem false_of_triple {U₀ V₀ : Subgroup T} [U₀.Normal] [V₀.Normal] (hsup : U₀ ⊔ V₀ = ⊤)
    (hcomm : ⁅U₀, V₀⁆ = ⊥)
    {P₁ S₁ : Type*} [Group P₁] [Group S₁] [IsSimpleGroup S₁] {ψ₁ : P₁ →* S₁}
    (hψ₁ : Function.Surjective ψ₁) (hk₁ : ψ₁.ker ≤ Subgroup.center P₁) {φ₁ : P₁ →* U₀}
    (hφ₁ : Function.Surjective φ₁)
    {P₂ S₂ : Type*} [Group P₂] [Group S₂] [IsSimpleGroup S₂] {ψ₂ : P₂ →* S₂}
    (hψ₂ : Function.Surjective ψ₂) (hk₂ : ψ₂.ker ≤ Subgroup.center P₂) {φ₂ : P₂ →* V₀}
    (hφ₂ : Function.Surjective φ₂)
    {U V W : Subgroup T} (hU : U.IsSubnormal) (hV : V.IsSubnormal) (hUp : Group.IsPerfect U)
    (hVp : Group.IsPerfect V) (hWp : Group.IsPerfect W) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥)
    (hW1 : W ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) (hUW : ⁅U, W⁆ = ⊥) (hVW : ⁅V, W⁆ = ⊥) : False := by
  have hZ := inf_le_center_of_commutator_eq_bot hsup hcomm
  have key : ∀ {X : Subgroup T}, Group.IsPerfect X → X ≠ ⊥ → X ≤ U₀ → X ≤ V₀ → False :=
    fun hXp hX1 h₁ h₂ => hX1 (eq_bot_of_isPerfect_of_le_center hXp ((le_inf h₁ h₂).trans hZ))
  have hUW' := le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ hφ₁ hψ₂ hk₂ hφ₂ hU hUp hWp hU1
    hW1 hUW
  have hVW' := le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ hφ₁ hψ₂ hk₂ hφ₂ hV hVp hWp hV1
    hW1 hVW
  have hUV' := le_or_le_of_commutator_eq_bot hsup hcomm hψ₁ hk₁ hφ₁ hψ₂ hk₂ hφ₂ hU hUp hVp hU1
    hV1 hUV
  rcases hUW' with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hVW' with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases hUV' with ⟨_, _⟩ | ⟨_, _⟩
  all_goals first
    | exact key hUp hU1 (by assumption) (by assumption)
    | exact key hVp hV1 (by assumption) (by assumption)
    | exact key hWp hW1 (by assumption) (by assumption)

theorem false_of_triple_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] [IsSimpleGroup H₁]
    [IsSimpleGroup H₂] {U V W : Subgroup (H₁ × H₂)} (hU : U.IsSubnormal) (hV : V.IsSubnormal)
    (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V) (hWp : Group.IsPerfect W)
    (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hW1 : W ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥) (hUW : ⁅U, W⁆ = ⊥)
    (hVW : ⁅V, W⁆ = ⊥) : False := by
  set U₀ := (MonoidHom.snd H₁ H₂).ker with hU₀
  set V₀ := (MonoidHom.fst H₁ H₂).ker with hV₀
  have hsup : U₀ ⊔ V₀ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have : ((a, b) : H₁ × H₂) = (a, 1) * (1, b) := by simp
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (by rw [hU₀, MonoidHom.mem_ker]; rfl))
      (Subgroup.mem_sup_right (by rw [hV₀, MonoidHom.mem_ker]; rfl))
  have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro ⟨a, b⟩ hab
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨a', b'⟩ hab'
    simp only [hU₀, hV₀, MonoidHom.mem_ker, MonoidHom.coe_snd] at hab hab'
    subst hab hab'
    simp
  set φ₁ : H₁ →* U₀ := (MonoidHom.inl H₁ H₂).codRestrict U₀
    (fun a => by rw [hU₀, MonoidHom.mem_ker]; rfl)
  set φ₂ : H₂ →* V₀ := (MonoidHom.inr H₁ H₂).codRestrict V₀
    (fun b => by rw [hV₀, MonoidHom.mem_ker]; rfl)
  have hφ₁ : Function.Surjective φ₁ := by
    rintro ⟨⟨a, b⟩, hab⟩
    simp only [hU₀, MonoidHom.mem_ker, MonoidHom.coe_snd] at hab
    subst hab
    exact ⟨a, rfl⟩
  have hφ₂ : Function.Surjective φ₂ := by
    rintro ⟨⟨a, b⟩, hab⟩
    simp only [hV₀, MonoidHom.mem_ker, MonoidHom.coe_fst] at hab
    subst hab
    exact ⟨b, rfl⟩
  have hid₁ : (MonoidHom.id H₁).ker ≤ Subgroup.center H₁ := by
    rw [MonoidHom.ker_id]; exact bot_le
  have hid₂ : (MonoidHom.id H₂).ker ≤ Subgroup.center H₂ := by
    rw [MonoidHom.ker_id]; exact bot_le
  exact false_of_triple hsup hcomm Function.surjective_id hid₁ hφ₁ Function.surjective_id hid₂
    hφ₂ hU hV hUp hVp hWp hU1 hV1 hW1 hUV hUW hVW

theorem false_of_triple_mulEquiv_prod {H₁ H₂ : Type*} [Group H₁] [Group H₂] [IsSimpleGroup H₁]
    [IsSimpleGroup H₂] (e : T ≃* H₁ × H₂) {U V W : Subgroup T} (hU : U.IsSubnormal)
    (hV : V.IsSubnormal) (hUp : Group.IsPerfect U) (hVp : Group.IsPerfect V)
    (hWp : Group.IsPerfect W) (hU1 : U ≠ ⊥) (hV1 : V ≠ ⊥) (hW1 : W ≠ ⊥) (hUV : ⁅U, V⁆ = ⊥)
    (hUW : ⁅U, W⁆ = ⊥) (hVW : ⁅V, W⁆ = ⊥) : False := by
  have hne : ∀ {X : Subgroup T}, X ≠ ⊥ → X.map e.toMonoidHom ≠ ⊥ := fun hX => by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
  have hc : ∀ {X X' : Subgroup T}, ⁅X, X'⁆ = ⊥ →
      ⁅X.map e.toMonoidHom, X'.map e.toMonoidHom⁆ = ⊥ := fun h => by
    rw [← Subgroup.map_commutator, h, Subgroup.map_bot]
  exact false_of_triple_prod (hU.map e.surjective) (hV.map e.surjective)
    (Group.IsPerfect.map _) (Group.IsPerfect.map _) (Group.IsPerfect.map _) (hne hU1) (hne hV1)
    (hne hW1) (hc hUV) (hc hUW) (hc hVW)

end Triple

section Item148

variable {G : Type} [Group G] [Finite G]

theorem false_of_triple_of_item148
    {A : Subgroup G} (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY A) :
    letI := ker148_normal hM.2
    ¬ Case1487 A (lB A) M →
      ∀ U V W : Subgroup ↥(img148 A M (deltaZero A (lB A) M)), U.IsSubnormal → V.IsSubnormal →
        Group.IsPerfect U → Group.IsPerfect V → Group.IsPerfect W → U ≠ ⊥ → V ≠ ⊥ → W ≠ ⊥ →
        ⁅U, V⁆ = ⊥ → ⁅U, W⁆ = ⊥ → ⁅V, W⁆ = ⊥ → False := by
  intro h7 U V W hU hV hUp hVp hWp hU1 hV1 hW1 hUV hUW hVW
  let := ker148_normal hM.2
  have hA5s : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA7s : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hA10s : IsSimpleGroup (alternatingGroup (Fin 10)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hid : ∀ (X : Type) [Group X], (MonoidHom.id X).ker ≤ Subgroup.center X := fun X _ => by
    rw [MonoidHom.ker_id]
    exact bot_le
  rcases (h148 M hM).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7'
  ·
    have hD : img148 A M (deltaZero A (lB A) M) = ⊥ := img148_eq_bot_of_le h1
    apply hU1
    rw [eq_bot_iff]
    intro x _
    have hx : (x : ↥(M ⊔ A) ⧸ ker148 A M) ∈ (⊥ : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) := by
      rw [← hD]
      exact x.2
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp hx))
  ·
    obtain ⟨c', -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, -, -, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    · exact false_of_mulEquiv_quasisimple (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1) φ
        hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · rcases hε with ⟨⟨φ⟩⟩ | ⟨h2q, ⟨φ⟩⟩
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField p f)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
      · have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two p f hf (by omega)
        exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · exact false_of_isTripleCover h6 hU hUp hVp hU1 hV1 hUV
    · exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨-, -, -, -, -, -, -, -, -, -, htypes⟩ := h3
    rcases htypes with hON | ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, -, hU6, hV6⟩ |
        ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hU6, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · have := CFSG.Sporadic.ON.isSimpleGroup_ON
      exact false_of_isTripleCover hON hU hUp hVp hU1 hV1 hUV
    ·
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      obtain ⟨hψ₂, hk₂⟩ := tripleCover_cover hV6.2.some
      exact false_of_triple hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀) Function.surjective_id
        hψ₂ hk₂ (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id hU hV hUp hVp hWp hU1 hV1 hW1
        hUV hUW hVW
    ·
      have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
        rw [eq_bot_iff, ← hinf]
        exact Subgroup.commutator_le_inf U₀ V₀
      obtain ⟨hψ₁, hk₁⟩ := tripleCover_cover hU6.2.some
      exact false_of_triple hsup hcomm hψ₁ hk₁ (φ₁ := MonoidHom.id ↥U₀) Function.surjective_id
        (ψ₂ := MonoidHom.id (alternatingGroup (Fin 5))) Function.surjective_id (hid _)
        (φ₂ := eV.symm.toMonoidHom) eV.symm.surjective hU hV hUp hVp hWp hU1 hV1 hW1 hUV hUW hVW
    ·
      exact false_of_triple_mulEquiv_prod φ hU hV hUp hVp hWp hU1 hV1 hW1 hUV hUW hVW
    ·
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    ·
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨-, -, -, n, -, -, -, hn, -, hiso, -⟩ := h5
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases hiso with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 2 (3 * n))
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
    · have h2 : 2 ^ (3 * n) ≠ 2 := by
        intro h22
        have := Nat.pow_right_injective (le_refl 2) (h22.trans (pow_one 2).symm)
        omega
      have := Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two 2 (3 * n) (by omega) h2
      exact false_of_mulEquiv_simple φ hU hUp hVp hU1 hV1 hUV
  ·
    obtain ⟨⟨φ⟩, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    exact false_of_triple_mulEquiv_prod φ hU hV hUp hVp hWp hU1 hV1 hW1 hUV hUW hVW
  ·
    exact h7 h7'

end Item148

section Images

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pPrimeCoreOf_map_of_injective (p : ℕ) {G' : Type} [Group G'] (f : G' →* G)
    (hf : Function.Injective f) (K : Subgroup G') :
    pPrimeCoreOf p (K.map f) = (pPrimeCoreOf p K).map f := by
  let ψ : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
  have h1 : (CFSG.pPrimeCore p ↥K).map ψ.toMonoidHom = CFSG.pPrimeCore p ↥(K.map f) :=
    CFSG.pPrimeCore_map_iso p ψ
  have h2 : (K.map f).subtype.comp ψ.toMonoidHom = f.comp K.subtype := by ext g; rfl
  unfold pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem pPrimeCoreOf_le_of_mem_thetaComponentsIn {M Y : Subgroup G}
    (hY : Y ∈ thetaComponentsIn M) : pPrimeCoreOf 3 Y ≤ pPrimeCoreOf 3 M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Y', hY', rfl⟩ := hY
  rw [pPrimeCoreOf_map_of_injective 3 M.subtype M.subtype_injective]
  exact Subgroup.map_mono (Proof153Twin2.map_pPrimeCore_le_of_isSubnormal' hY'.2.1)

variable {A M : Subgroup G} [(ker148 A M).Normal]

omit [Finite G] in
theorem isPerfect_img_subgroupOf {Z D : Subgroup G} (hZD : Z ≤ D) (hDM : D ≤ M ⊔ A)
    [Group.IsPerfect Z] : Group.IsPerfect ((img148 A M Z).subgroupOf (img148 A M D)) := by
  have hle : img148 A M Z ≤ img148 A M D := img148_mono hZD
  have : Group.IsPerfect ↥(img148 A M Z) := isPerfect_img148 (hZD.trans hDM)
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (MulEquiv.surjective _)

omit [Finite G] in
theorem commutator_img_subgroupOf_eq_bot {Z Z' D : Subgroup G} (hZD : Z ≤ D) (hZ'D : Z' ≤ D)
    (hDM : D ≤ M ⊔ A) (hc : ⁅Z, Z'⁆ ≤ pPrimeCoreOf 3 M) :
    ⁅(img148 A M Z).subgroupOf (img148 A M D), (img148 A M Z').subgroupOf (img148 A M D)⁆ =
      ⊥ := by
  have h1 : ⁅img148 A M Z, img148 A M Z'⁆ = ⊥ := by
    rw [← Item148PtRes.img148_commutator (hZD.trans hDM) (hZ'D.trans hDM)]
    exact img148_eq_bot_of_le hc
  refine (Subgroup.map_eq_bot_iff_of_injective _ (img148 A M D).subtype_injective).mp ?_
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (img148_mono hZD), inf_eq_left.mpr (img148_mono hZ'D)]
  exact h1

theorem img_subgroupOf_ne_bot {Z D : Subgroup G} (hZD : Z ≤ D) (hDM : D ≤ M ⊔ A) {x : G}
    (hx : x ∈ Z) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    (img148 A M Z).subgroupOf (img148 A M D) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h0
  rw [Subgroup.subgroupOf_eq_bot] at h0
  have hxM : x ∈ M ⊔ A := hDM (hZD hx)
  set y := QuotientGroup.mk' (ker148 A M) ⟨x, hxM⟩ with hy
  have hyZ : y ∈ img148 A M Z := ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hy1 : y = 1 := (Subgroup.disjoint_def.mp h0) hyZ (img148_mono hZD hyZ)
  rw [hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy1
  have hxO : x ∈ pPrimeCoreOf 3 M := Subgroup.mem_subgroupOf.mp hy1
  have h3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 M) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 M) h
  exact hx1 (eq_one_of_mem_of_pow_three h3 hxO hx3)

omit [Finite G] in
theorem isSubnormal_img_subgroupOf {Z D : Subgroup G} (hAM : A ≤ M)
    (hZ : Z ∈ thetaComponentsIn M) :
    ((img148 A M Z).subgroupOf (img148 A M D)).IsSubnormal := by
  have hMA : M = M ⊔ A := (sup_eq_left.mpr hAM).symm
  obtain ⟨-, hZ₁⟩ := Proof153Twin2.subgroupOf_mem_thetaComponents hMA hZ
  have hsn : (img148 A M Z).IsSubnormal := hZ₁.2.1.map (QuotientGroup.mk'_surjective _)
  exact hsn.subgroupOf

end Images

section Main

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_mem_thetaComponentsIn {K Z Z' : Subgroup G}
    (hZ : Z ∈ thetaComponentsIn K) (hZ' : Z' ∈ thetaComponentsIn K) (hne : Z ≠ Z') :
    ⁅Z, Z'⁆ ≤ (aschbacherSolvableCore 3 ↥K).map K.subtype := by
  obtain ⟨Z₁, hZ₁, rfl⟩ := hZ
  obtain ⟨Z₂, hZ₂, rfl⟩ := hZ'
  have hne' : Z₁ ≠ Z₂ := fun h => hne (h ▸ rfl)
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (commutator_le_of_mem_thetaComponents hZ₁ hZ₂ hne')

theorem map_aschbacherSolvableCore_le_pPrimeCoreOf (K : Subgroup G) :
    (aschbacherSolvableCore 3 ↥K).map K.subtype ≤ pPrimeCoreOf 3 K := by
  obtain ⟨-, hθc, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three
  have : (aschbacherSolvableCore 3 ↥K).Normal := Subgroup.normal_of_characteristic _
  exact Subgroup.map_mono
    (le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3⟩)

theorem normalizer_map_conj_le
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A))
    {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A))
    (h7 : ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
      ¬ M ≤ Subgroup.normalizer (Y : Set G) →
      ∀ hAN : A ≤ Subgroup.normalizer (M : Set G),
        letI := ker148_normal hAN
        ¬ Case1487 A (lB A) M)
    {M : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G))
    {m : G} (hm : m ∈ M) :
    Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Y : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro n hn
  by_contra hnY
  set Y₁ := Y.map (MulAut.conj m).toMonoidHom with hY₁
  obtain ⟨hYM, hAM, hM2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM
  have hnc := Proof153Twin.hasNonCentralThree_of_mem_scriptY4 hY.prop.1
  have horb : ∀ t ∈ M, A ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    fun t ht => le_normalizer_map_conj_of_hasNonCentralThree h h152 hY hnc hM ht
  have hMX₀ : M ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M) : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hM2.1
  have hYX₀ : Y ≤ oPrimeResidualOf 3 (delta A (lB A) M) := le_oPrimeResidualOf_delta hY.prop.1 hYM
  have hconj : ∀ g ∈ M, Y.map (MulAut.conj g).toMonoidHom ≤
      oPrimeResidualOf 3 (delta A (lB A) M) := by
    rintro g hg _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMX₀ hg) y).mp (hYX₀ hy)
  have hX₀N : oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (Y : Set G) :=
    (oPrimeResidualOf_delta_le_of_forall_conj h149 hM2.1 horb).trans
      ((Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le _))
  have hY₁N : Y₁ ≤ Subgroup.normalizer (Y : Set G) := (hconj m hm).trans hX₀N
  have hYN₁ : Y ≤ Subgroup.normalizer (Y₁ : Set G) := by
    intro y hy
    have h1 : m⁻¹ * y * m ∈ Subgroup.normalizer (Y : Set G) :=
      (hconj m⁻¹ (M.inv_mem hm)).trans hX₀N ⟨y, hy, by simp⟩
    have h2 : Y.map (MulAut.conj (m⁻¹ * y * m)).toMonoidHom = Y :=
      Late.map_conj_eq_of_mem_normalizer h1
    have h3 : Y₁.map (MulAut.conj y).toMonoidHom = Y₁ := by
      rw [hY₁, Late.map_conj_map_conj]
      calc Y.map (MulAut.conj (y * m)).toMonoidHom
          = (Y.map (MulAut.conj (m⁻¹ * y * m)).toMonoidHom).map
              (MulAut.conj m).toMonoidHom := by
            rw [Late.map_conj_map_conj, show m * (m⁻¹ * y * m) = y * m by group]
        _ = Y.map (MulAut.conj m).toMonoidHom := by rw [h2]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h3
  have hAN₁ : A ≤ Subgroup.normalizer (Y₁ : Set G) := horb m hm
  have hYY₁ : Y ≠ Y₁ := by
    intro he
    apply hnY
    rw [he]
    exact hn
  have hP₁ : CFSG.Open.pCoreOf 2 Y₁ ≠ ⊥ := by
    rw [hY₁, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj m) Y, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj m).injective]
    exact hY.prop.2.2
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₁) hP₁
  obtain ⟨M₁, hle, hM₁⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hN₁ : Subgroup.normalizer (Y₁ : Set G) ≤ M₁ :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₁).trans hle
  have hM₁m : M₁ ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM₁, fun x hx => hN₁ (sup_le hYN₁ hAN₁ hx)⟩
  have hnM₁ : n ∈ M₁ := hN₁ hn
  have hM₁Y : ¬ M₁ ≤ Subgroup.normalizer (Y : Set G) := fun hle' => hnY (hle' hnM₁)
  obtain ⟨hYM₁, hAM₁, hM₁2, -⟩ := facts_of_mem_maximalTwoLocalsContaining h hM₁m
  have hAN : A ≤ Subgroup.normalizer (M₁ : Set G) := hM₁2.1.2
  let := ker148_normal hAN
  set Yn := Y.map (MulAut.conj n).toMonoidHom with hYn
  have hYθ₁ : Y ∈ thetaComponentsIn M₁ := mem_thetaComponentsIn_of_item152 h h152 hY hM₁m
  have hYnθ₁ : Yn ∈ thetaComponentsIn M₁ :=
    map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer hnM₁) hYθ₁
  have hYYn : Y ≠ Yn := fun he =>
    hnY (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hYθ : Y ∈ thetaComponentsIn M := mem_thetaComponentsIn_of_item152 h h152 hY hM
  have hY₁θ : Y₁ ∈ thetaComponentsIn M :=
    map_conj_mem_thetaComponentsIn (Subgroup.le_normalizer hm) hYθ
  obtain ⟨heq149, -, -⟩ := h149 M₁ hM₁2.1
  have hX₁D : oPrimeResidualOf 3 (delta A (lB A) M₁) ≤ deltaZero A (lB A) M₁ := by
    rw [heq149]
    exact (Sec14.oPrimeResidualOf_le_self 3 _).trans (Sec14.inSubgroup_oResidual_le_self 2 _)
  have hM₁X₁ : M₁ ≤ Subgroup.normalizer (oPrimeResidualOf 3 (delta A (lB A) M₁) : Set G) :=
    normalizer_le_normalizer_oPrimeResidualOf_delta h149 hM₁2.1
  have hYX₁ : Y ≤ oPrimeResidualOf 3 (delta A (lB A) M₁) :=
    le_oPrimeResidualOf_delta hY.prop.1 hYM₁
  have hYD : Y ≤ deltaZero A (lB A) M₁ := hYX₁.trans hX₁D
  have hYnD : Yn ≤ deltaZero A (lB A) M₁ := by
    refine le_trans ?_ hX₁D
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hM₁X₁ hnM₁) y).mp (hYX₁ hy)
  have hY₁D : Y₁ ≤ deltaZero A (lB A) M₁ := by
    have horb₁ : ∀ t ∈ M, A ≤ Subgroup.normalizer
        ((Y₁.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
      intro t ht
      rw [hY₁, Late.map_conj_map_conj]
      exact horb (t * m) (M.mul_mem ht hm)
    refine ((hconj m hm).trans ?_).trans hX₁D
    exact (oPrimeResidualOf_delta_le_of_forall_conj h149 hM2.1 horb₁).trans
      (oPrimeResidualOf_mono 3 (delta_mono hN₁))
  have hDM : deltaZero A (lB A) M₁ ≤ M₁ ⊔ A := (deltaZero_le M₁).trans le_sup_left
  have hcYYn : ⁅Y, Yn⁆ ≤ pPrimeCoreOf 3 M₁ :=
    (commutator_le_of_mem_thetaComponentsIn hYθ₁ hYnθ₁ hYYn).trans
      (map_aschbacherSolvableCore_le_pPrimeCoreOf M₁)
  have hcYY₁ : ⁅Y, Y₁⁆ ≤ pPrimeCoreOf 3 M₁ := by
    obtain ⟨hθN, -, hθ3⟩ := map_aschbacherSolvableCore_facts M
    have h1 : ⁅Y, Y₁⁆ ≤ (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y :=
      le_inf (commutator_le_of_mem_thetaComponentsIn hYθ hY₁θ hYY₁)
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hY₁N)
    have h2 : (aschbacherSolvableCore 3 ↥M).map M.subtype ⊓ Y ≤ pPrimeCoreOf 3 Y := by
      refine Sec14.le_pPrimeCoreOf inf_le_right
        (Late.le_normalizer_inf (hYM.trans hθN) Subgroup.le_normalizer) ?_
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        hθ3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
    exact (h1.trans h2).trans (pPrimeCoreOf_le_of_mem_thetaComponentsIn hYθ₁)
  have hcYnY₁ : ⁅Yn, Y₁⁆ ≤ pPrimeCoreOf 3 M₁ := by
    have hY₁n : Y₁.map (MulAut.conj n).toMonoidHom = Y₁ := Late.map_conj_eq_of_mem_normalizer hn
    have hOn : (pPrimeCoreOf 3 M₁).map (MulAut.conj n).toMonoidHom = pPrimeCoreOf 3 M₁ :=
      Late.map_conj_eq_of_mem_normalizer (Sec14.le_normalizer_pPrimeCoreOf 3 M₁ hnM₁)
    rw [hYn, ← hY₁n, ← Subgroup.map_commutator, ← hOn]
    exact Subgroup.map_mono hcYY₁
  have hYp : Group.IsPerfect ↥Y := isPerfect_of_mem_scriptY4 hY.prop.1
  have hYnp : Group.IsPerfect ↥Yn := Group.IsPerfect.map _
  have hY₁p : Group.IsPerfect ↥Y₁ := Group.IsPerfect.map _
  obtain ⟨x, hxY, hx3, y, hyY, hxy⟩ := hnc
  have hx1 : x ≠ 1 := by
    rintro rfl
    apply hxy
    rw [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact one_mem _
  have hconj1 : ∀ g : G, MulAut.conj g x ≠ 1 := fun g h1 =>
    hx1 ((MulAut.conj g).injective (h1.trans (map_one _).symm))
  have hconj3 : ∀ g : G, (MulAut.conj g x) ^ 3 = 1 := fun g => by rw [← map_pow, hx3, map_one]
  exact false_of_triple_of_item148 h148 hM₁2.1 (h7 M₁ hM₁m hM₁Y hAN) _ _ _
    (isSubnormal_img_subgroupOf hAM₁ hYθ₁) (isSubnormal_img_subgroupOf hAM₁ hYnθ₁)
    (isPerfect_img_subgroupOf hYD hDM) (isPerfect_img_subgroupOf hYnD hDM)
    (isPerfect_img_subgroupOf hY₁D hDM)
    (img_subgroupOf_ne_bot hYD hDM hxY hx3 hx1)
    (img_subgroupOf_ne_bot hYnD hDM ⟨x, hxY, rfl⟩ (hconj3 n) (hconj1 n))
    (img_subgroupOf_ne_bot hY₁D hDM ⟨x, hxY, rfl⟩ (hconj3 m) (hconj1 m))
    (commutator_img_subgroupOf_eq_bot hYD hYnD hDM hcYYn)
    (commutator_img_subgroupOf_eq_bot hYD hY₁D hDM hcYY₁)
    (commutator_img_subgroupOf_eq_bot hYnD hY₁D hDM hcYnY₁)

end Main

end Proof153Twin3

open Proof153Twin3

variable {G : Type} [Group G] [Finite G]

theorem claim153TwinNorm_of
    {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A)) (h152 : Item152 A (lB A))
    (h7 : ∀ Y ∈ scriptY0Star A (lB A), ¬ HasFaithfulE9 Y →
      ∀ M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G),
        ¬ M ≤ Subgroup.normalizer (Y : Set G) →
        ∀ hAN : A ≤ Subgroup.normalizer (M : Set G),
          letI := ker148_normal hAN
          ¬ Case1487 A (lB A) M) :
    Claim153TwinNorm A (lB A) := by
  intro Y hY hE M hM _ m hm
  have hle := normalizer_map_conj_le h h148 h149 h152 hY (h7 Y hY hE) hM hm
  have hmap : (Subgroup.normalizer (Y : Set G)).map (MulAut.conj m).toMonoidHom =
      Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq Y (MulAut.conj m)
  have hcard : Nat.card (Subgroup.normalizer (Y : Set G)) ≤
      Nat.card (Subgroup.normalizer ((Y.map (MulAut.conj m).toMonoidHom : Subgroup G) :
        Set G)) := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj m).injective]
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).ge

theorem claim153TwinNormR_of
    (h148 : Item148R) (h149 : Sec16.Item149S14) (h152 : Item152R) : Claim153TwinNormR :=
  fun G _ _ A c L hR => claim153TwinNorm_of hR.toSec14Std (h148 G A c L hR)
    (h149 G A c L hR.toSec14Std) (h152 G A c L hR)
    (claim153TwinCase7_of h149 h152 G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
