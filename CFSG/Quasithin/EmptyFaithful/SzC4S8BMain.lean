module

public import CFSG.Quasithin.EmptyFaithful.SzC4S8Mod
public import CFSG.Quasithin.EmptyFaithful.SzC4S8Cocycle
public import CFSG.Quasithin.EmptyFaithful.SzC4S8BVec
public import CFSG.Quasithin.EmptyFaithful.SBc11Blocks
public import CFSG.Quasithin.EmptyFaithful.SBc11MS
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.SBc11
open scoped commutatorElement Pointwise

@[expose] def C134Case4RigidAt {G : Type} [Group G] (G₀ L : Subgroup G) : Prop :=
  ∀ c ∈ c134CQ G₀ L, (∀ g ∈ G₀, g * c * g⁻¹ = c) →
    ∀ x ∈ c134Q G₀ L, (∀ q ∈ c134Q G₀ L, ⁅x, q⁆ = 1 ∨ ⁅x, q⁆ = c) →
      ∀ q ∈ c134Q G₀ L, x * q = q * x

section Phi

variable {G : Type} [Group G]

theorem s8b_phi_mul {Q : Subgroup G} {c₀ g h : G} (hc₀sq : c₀ * c₀ = 1) (hgc : g * c₀ = c₀ * g)
    (hg : ∀ q ∈ Q, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = c₀ * q)
    (hh : ∀ q ∈ Q, h * q * h⁻¹ = q ∨ h * q * h⁻¹ = c₀ * q) :
    ∀ q ∈ Q, g * h * q * (g * h)⁻¹ = q ∨ g * h * q * (g * h)⁻¹ = c₀ * q := by
  intro q hq
  have e : g * h * q * (g * h)⁻¹ = g * (h * q * h⁻¹) * g⁻¹ := by group
  rcases hh q hq with h1 | h1
  · rw [e, h1]
    exact hg q hq
  · have e2 : g * (c₀ * q) * g⁻¹ = c₀ * (g * q * g⁻¹) := by
      have hc : g * c₀ * g⁻¹ = c₀ := by
        calc g * c₀ * g⁻¹ = c₀ * g * g⁻¹ := by rw [hgc]
          _ = c₀ := by group
      calc g * (c₀ * q) * g⁻¹ = (g * c₀ * g⁻¹) * (g * q * g⁻¹) := by group
        _ = c₀ * (g * q * g⁻¹) := by rw [hc]
    rw [e, h1, e2]
    rcases hg q hq with h2 | h2
    · exact Or.inr (by rw [h2])
    · refine Or.inl ?_
      rw [h2, ← mul_assoc, hc₀sq, one_mul]

theorem s8b_phi_inv {Q : Subgroup G} {c₀ g : G} (hc₀sq : c₀ * c₀ = 1) (hgc : g * c₀ = c₀ * g)
    (hg : ∀ q ∈ Q, g * q * g⁻¹ = q ∨ g * q * g⁻¹ = c₀ * q) :
    ∀ q ∈ Q, g⁻¹ * q * g⁻¹⁻¹ = q ∨ g⁻¹ * q * g⁻¹⁻¹ = c₀ * q := by
  intro q hq
  have hc : g⁻¹ * c₀ * g = c₀ := by
    calc g⁻¹ * c₀ * g = g⁻¹ * (c₀ * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * c₀) := by rw [hgc]
      _ = c₀ := by group
  rw [inv_inv]
  rcases hg q hq with h | h
  · refine Or.inl ?_
    have h' : g * q = q * g := by
      have := congrArg (· * g) h
      simpa [mul_assoc] using this
    calc g⁻¹ * q * g = g⁻¹ * (q * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * q) := by rw [h']
      _ = q := by group
  · refine Or.inr ?_
    have h' : g⁻¹ * (c₀ * q) * g = q := by
      calc g⁻¹ * (c₀ * q) * g = g⁻¹ * (g * q * g⁻¹) * g := by rw [h]
        _ = q := by group
    have e : g⁻¹ * (c₀ * q) * g = c₀ * (g⁻¹ * q * g) := by
      calc g⁻¹ * (c₀ * q) * g = (g⁻¹ * c₀ * g) * (g⁻¹ * q * g) := by group
        _ = c₀ * (g⁻¹ * q * g) := by rw [hc]
    rw [e] at h'
    calc g⁻¹ * q * g = c₀ * (c₀ * (g⁻¹ * q * g)) := by rw [← mul_assoc, hc₀sq, one_mul]
      _ = c₀ * q := by rw [h']

end Phi

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem s8_case4_false_of_rigidAt (h113 : StageLemma14113)
    (c : Ctx15331 T Mc M V₁ V₂ Yp I L t)
    (hlist : IsPSL 3 2 1 ↥(Star153 T I L) ∨ IsAlt 6 ↥(Star153 T I L) ∨
      IsPSU 3 3 1 ↥(Star153 T I L))
    (h : MS93.IsC134Case4Corr I (Sgp153 T V₁) L)
    (hR : (∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ∧ IsModO2Surj L α) → C134Case4RigidAt I L) : False := by
  classical
  have hset := coe_eq_mul_of_ctx c
  obtain ⟨⟨n, F, _, _, α, hcard, hmod, hE2, -, hdisj, hU, -, -, -⟩, -⟩ := id h
  obtain ⟨hn, -⟩ := sl3_case c hlist hcard hmod
  subst hn
  have hF2 : Fintype.card F = 2 := by simpa using hcard
  have hRc := hR ⟨F, inferInstance, inferInstance, α, hF2, hmod⟩
  unfold C134Case4RigidAt at hRc
  obtain ⟨c₀, u₀, v, hc₀C, hc₀1, hc₀V₁, hvV₁, hv1, hvc, hVall, hcomm, hc₀S, hsv, hu₀U, hu₀1, hu₀S, y₀,
    hy₀, hy₀mv⟩ := s8b_vectors h113 c hF2 hE2 hdisj hU
  obtain ⟨-, hLI, hIL, -, hsyl, hperf⟩ := ctx_basic c
  have c25 : Ctx15325L T Mc M V₁ V₂ Yp I L t := c.toCtx15328.toCtx15327.toCtx15325L
  have hyp : Hyp15310 G T Mc M V₁ V₂ Yp t := c25.ctx.hyp
  have hdec : Decomp153 T M V₁ V₂ t := hyp.decomp
  have hSI : Sgp153 T V₁ ≤ I := hsyl.1
  have hQS : c134Q I L ≤ Sgp153 T V₁ := s8_Q_le_S c
  have hQN : I ≤ Subgroup.normalizer (c134Q I L : Set G) := s8_I_le_normalizer_Q c
  have hLQ : L ≤ Subgroup.normalizer (c134Q I L : Set G) := hLI.trans hQN
  have hZN : ∀ g ∈ Subgroup.normalizer (c134Q I L : Set G),
      g ∈ Subgroup.normalizer ((centerOf (c134Q I L) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hg, S153F.mem_normalizer_centralizer_of_mem_normalizer hg⟩
  have hLZ : L ≤ Subgroup.normalizer ((centerOf (c134Q I L) : Subgroup G) : Set G) :=
    fun l hl => hZN l (hLQ hl)
  have hUZ : ⁅centerOf (c134Q I L), L⁆ ≤ centerOf (c134Q I L) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLZ
  have hZQ : centerOf (c134Q I L) ≤ c134Q I L := inf_le_left
  have hZab : ∀ a ∈ centerOf (c134Q I L), ∀ b ∈ centerOf (c134Q I L), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp ha.2 b (hZQ hb)).symm
  have hQL : c134Q I L ≤ L :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((pCoreOf_le 2 I).trans hIL)
  have hV₁S : V₁ ≤ Sgp153 T V₁ :=
    le_inf (hdec.le₁.trans hyp.hyp.VZ_le_T) Subgroup.le_normalizer
  have hvN : v ∈ Subgroup.normalizer (L : Set G) := hIL (hSI (hV₁S hvV₁))
  have hc₀L : ∀ l ∈ L, l * c₀ = c₀ * l := fun l hl =>
    Subgroup.mem_centralizer_iff.mp hc₀C.2 l hl
  have hc₀sq : c₀ * c₀ = 1 := by
    have := s8_sq_eq_one_of_isE2 hE2 ⟨c₀, hc₀C⟩
    exact congrArg Subtype.val this
  have hvQ : ∀ q ∈ c134Q I L, v * q * v⁻¹ = q ∨ v * q * v⁻¹ = c₀ * q := by
    intro q hq
    rcases hsv q (hQS hq) with h1 | h1
    · refine Or.inl ?_
      have h2 : q * v = v * q := by
        have := congrArg (· * q) h1
        simpa [mul_assoc] using this
      calc v * q * v⁻¹ = q * v * v⁻¹ := by rw [h2]
        _ = q := by group
    · refine Or.inr ?_
      have h2 : q * v = c₀ * v * q := by
        have := congrArg (· * q) h1
        simpa [mul_assoc] using this
      have h3 : v * q = c₀ * q * v := by
        calc v * q = c₀ * (c₀ * (v * q)) := by rw [← mul_assoc, hc₀sq, one_mul]
          _ = c₀ * (c₀ * v * q) := by rw [mul_assoc c₀ v q]
          _ = c₀ * (q * v) := by rw [h2]
          _ = c₀ * q * v := by rw [mul_assoc]
      calc v * q * v⁻¹ = c₀ * q * v * v⁻¹ := by rw [h3]
        _ = c₀ * q := by group
  have hlvQ : ∀ l ∈ L, ∀ q ∈ c134Q I L,
      (l * v * l⁻¹) * q * (l * v * l⁻¹)⁻¹ = q ∨
        (l * v * l⁻¹) * q * (l * v * l⁻¹)⁻¹ = c₀ * q := by
    intro l hl q hq
    have hq' : l⁻¹ * q * l ∈ c134Q I L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem hl)) q).mp hq
      simpa using this
    have hlc : l * c₀ * l⁻¹ = c₀ := by
      calc l * c₀ * l⁻¹ = c₀ * l * l⁻¹ := by rw [hc₀L l hl]
        _ = c₀ := by group
    have e : (l * v * l⁻¹) * q * (l * v * l⁻¹)⁻¹ =
        l * (v * (l⁻¹ * q * l) * v⁻¹) * l⁻¹ := by group
    rw [e]
    rcases hvQ _ hq' with h1 | h1
    · rw [h1]
      exact Or.inl (by group)
    · rw [h1]
      refine Or.inr ?_
      calc l * (c₀ * (l⁻¹ * q * l)) * l⁻¹ = (l * c₀ * l⁻¹) * q := by group
        _ = c₀ * q := by rw [hlc]
  have hlvc : ∀ l ∈ L, (l * v * l⁻¹) * c₀ = c₀ * (l * v * l⁻¹) := by
    intro l hl
    have h1 : l⁻¹ * c₀ = c₀ * l⁻¹ := by
      have := hc₀L l⁻¹ (L.inv_mem hl)
      exact this
    calc (l * v * l⁻¹) * c₀ = l * v * (l⁻¹ * c₀) := by rw [mul_assoc (l * v) l⁻¹ c₀]
      _ = l * v * (c₀ * l⁻¹) := by rw [h1]
      _ = l * (v * c₀) * l⁻¹ := by group
      _ = l * (c₀ * v) * l⁻¹ := by rw [← hcomm]
      _ = (l * c₀) * v * l⁻¹ := by group
      _ = (c₀ * l) * v * l⁻¹ := by rw [hc₀L l hl]
      _ = c₀ * (l * v * l⁻¹) := by group
  let ε : G → G := fun l => v⁻¹ * (l * v * l⁻¹)
  have hcoc : ∀ a ∈ L, ∀ b ∈ L, ε (a * b) = ε a * (a * ε b * a⁻¹) := by
    intro a _ b _
    simp only [ε]
    group
  have hεL : ∀ l ∈ L, ε l ∈ L := by
    intro l hl
    have h1 : v⁻¹ * l * v ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hvN) l).mp hl
      simpa [mul_assoc] using this
    have : ε l = (v⁻¹ * l * v) * l⁻¹ := by
      simp only [ε]
      group
    rw [this]
    exact L.mul_mem h1 (L.inv_mem hl)
  have hc₀I : ∀ g ∈ I, g * c₀ * g⁻¹ = c₀ := by
    intro g hg
    have hg' : g ∈ (L : Set G) * (Sgp153 T V₁ : Set G) := by
      rw [← hset]
      exact hg
    obtain ⟨l, hl, s, hs, rfl⟩ := Set.mem_mul.mp hg'
    have hsc : s * c₀ * s⁻¹ = c₀ := by
      calc s * c₀ * s⁻¹ = c₀ * s * s⁻¹ := by rw [hc₀S s hs]
        _ = c₀ := by group
    have hlc : l * c₀ * l⁻¹ = c₀ := by
      calc l * c₀ * l⁻¹ = c₀ * l * l⁻¹ := by rw [hc₀L l hl]
        _ = c₀ := by group
    calc l * s * c₀ * (l * s)⁻¹ = l * (s * c₀ * s⁻¹) * l⁻¹ := by group
      _ = c₀ := by rw [hsc, hlc]
  have hLU : ∀ l ∈ L, l ∈ Subgroup.normalizer ((⁅centerOf (c134Q I L), L⁆ : Subgroup G) : Set G) :=
    fun l hl => S153H.mem_normalizer_commutator (hLZ hl) (Subgroup.le_normalizer hl)
  have hUker : ∀ k ∈ L, (∀ u ∈ ⁅centerOf (c134Q I L), L⁆, k * u * k⁻¹ = u) →
      k ∈ pCoreOf 2 L := by
    intro k hk hkU
    have h1 : α ⟨k, hk⟩ = 1 := s8_alpha_eq_one hU (l := ⟨k, hk⟩) hkU
    have h2 : (⟨k, hk⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hmod.2]
      exact h1
    exact (CFSG.QuasithinUnique.AppC.mem_pCore_iff_mem_blockQ (⟨k, hk⟩ : ↥L)).1 h2
  have hεΦ : ∀ l ∈ L, ∀ q ∈ c134Q I L,
      ε l * q * (ε l)⁻¹ = q ∨ ε l * q * (ε l)⁻¹ = c₀ * q := by
    intro l hl
    have hvc' : v⁻¹ * c₀ = c₀ * v⁻¹ := by
      have := congrArg (v⁻¹ * · * v⁻¹) hcomm
      simpa [mul_assoc] using this
    have hvinv := s8b_phi_inv (Q := c134Q I L) hc₀sq hcomm.symm hvQ
    exact s8b_phi_mul (Q := c134Q I L) hc₀sq hvc' hvinv (hlvQ l hl)
  have hεO : ∀ l ∈ L, ε l ∈ pCoreOf 2 L := by
    intro l hl
    refine hUker (ε l) (hεL l hl) fun u hu => ?_
    rcases hεΦ l hl u (hZQ (hUZ hu)) with h | h
    · exact h
    · exfalso
      have hmemU : ε l * u * (ε l)⁻¹ ∈ ⁅centerOf (c134Q I L), L⁆ :=
        (Subgroup.mem_normalizer_iff.mp (hLU _ (hεL l hl)) u).mp hu
      rw [h] at hmemU
      have hc₀U : c₀ ∈ ⁅centerOf (c134Q I L), L⁆ := by
        have := Subgroup.mul_mem _ hmemU (Subgroup.inv_mem _ hu)
        simpa [mul_assoc] using this
      have hmem : c₀ ∈ c134CQ I L ⊓ ⁅centerOf (c134Q I L), L⁆ := ⟨hc₀C, hc₀U⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact hc₀1 hmem
  have hQ2 : IsPGroup 2 ↥(c134Q I L) := hsyl.2.1.to_le hQS
  have hQcore : c134Q I L ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hQL hLQ hQ2
  have hKL' : ⁅pCoreOf 2 L, L⁆ ≤ c134Q I L :=
    Subgroup.commutator_mono (s8_pCore_L_le c) le_rfl
  have hKK' : ⁅pCoreOf 2 L, pCoreOf 2 L⁆ ≤ c134Q I L :=
    (Subgroup.commutator_mono le_rfl (pCoreOf_le 2 L)).trans hKL'
  have hεQ : ∀ l ∈ L, ε l ∈ c134Q I L :=
    SzC4S8.cocycle_mem_of_perfect hperf hQcore hKL' hKK' ε hεO hcoc
  have hεC : ∀ l ∈ L, ε l ∈ Subgroup.centralizer (c134Q I L : Set G) := by
    intro l hl
    have hcomm' : ∀ q ∈ c134Q I L, ⁅ε l, q⁆ = 1 ∨ ⁅ε l, q⁆ = c₀ := by
      intro q hq
      rcases hεΦ l hl q hq with h1 | h1
      · refine Or.inl ?_
        simp only [commutatorElement_def]
        rw [h1]
        group
      · refine Or.inr ?_
        simp only [commutatorElement_def]
        rw [h1]
        group
    refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
    exact (hRc c₀ hc₀C hc₀I (ε l) (hεQ l hl) hcomm' q hq).symm
  have hKker : ∀ k ∈ L ⊓ Subgroup.centralizer (c134Q I L : Set G), k ∈ pCoreOf 2 L := by
    intro k hk
    refine hUker k hk.1 fun u hu => ?_
    have h := Subgroup.mem_centralizer_iff.mp hk.2 u (hZQ (hUZ hu))
    calc k * u * k⁻¹ = u * k * k⁻¹ := by rw [h]
      _ = u := by group
  have hKL : ⁅L ⊓ Subgroup.centralizer (c134Q I L : Set G), L⁆ ≤
      (L ⊓ Subgroup.centralizer (c134Q I L : Set G)) ⊓ centerOf (c134Q I L) := by
    rw [Subgroup.commutator_le]
    intro k hk l hl
    have hKk : l * k⁻¹ * l⁻¹ ∈ L ⊓ Subgroup.centralizer (c134Q I L : Set G) :=
      ⟨L.mul_mem (L.mul_mem hl (L.inv_mem hk.1)) (L.inv_mem hl),
        S153F.conj_mem_centralizer_of_mem_normalizer (hLQ hl)
          ((Subgroup.centralizer (c134Q I L : Set G)).inv_mem hk.2)⟩
    have hcm : ⁅k, l⁆ = k * (l * k⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hmem : ⁅k, l⁆ ∈ L ⊓ Subgroup.centralizer (c134Q I L : Set G) := by
      rw [hcm]
      exact Subgroup.mul_mem _ hk hKk
    refine ⟨hmem, ?_, hmem.2⟩
    exact Subgroup.commutator_mem_commutator (s8_pCore_L_le c (hKker k hk)) hl
  have hεN : ∀ l ∈ L, ε l ∈ (L ⊓ Subgroup.centralizer (c134Q I L : Set G)) ⊓
      centerOf (c134Q I L) :=
    SzC4S8.cocycle_mem_of_perfect hperf inf_le_left hKL
      ((Subgroup.commutator_mono le_rfl inf_le_left).trans hKL) ε
      (fun l hl => ⟨hεL l hl, hεC l hl⟩) hcoc
  have hKK2 : ⁅centerOf (c134Q I L), centerOf (c134Q I L)⁆ ≤ ⁅centerOf (c134Q I L), L⁆ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZab a ha b hb)]
    exact Subgroup.one_mem _
  have hεU : ∀ l ∈ L, ε l ∈ ⁅centerOf (c134Q I L), L⁆ :=
    SzC4S8.cocycle_mem_of_perfect hperf hUZ le_rfl hKK2 ε (fun l hl => (hεN l hl).2) hcoc
  have hεM : ∀ m ∈ L ⊓ Subgroup.centralizer ({v} : Set G), ε m = 1 := by
    intro m hm
    have hvm : m * v = v * m := Subgroup.mem_centralizer_singleton_iff.mp hm.2
    simp only [ε]
    rw [hvm]
    group
  have hSLM : ∀ s ∈ Sgp153 T V₁ ⊓ L, s ∈ L ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro s hs
    refine ⟨hs.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rcases hsv s hs.1 with h | h
    · calc s * v = (s * v * s⁻¹) * s := by group
        _ = v * s := by rw [h]
    · exfalso
      have hεs : ε s = c₀ := by
        simp only [ε]
        rw [h]
        calc v⁻¹ * (c₀ * v) = v⁻¹ * (v * c₀) := by rw [hcomm]
          _ = c₀ := by group
      have hmem : c₀ ∈ c134CQ I L ⊓ ⁅centerOf (c134Q I L), L⁆ := ⟨hc₀C, hεs ▸ hεU s hs.2⟩
      rw [hdisj, Subgroup.mem_bot] at hmem
      exact hc₀1 hmem
  have hYM : ∀ y ∈ Yp, y ∈ L ⊓ Subgroup.centralizer ({v} : Set G) := fun y hy =>
    ⟨c.c27.Yp_le hy, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (c.c29.cent hy) v hvV₁).symm⟩
  have hsylL : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hsyl hLI
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mpr hIL).isSubnormal
  have hB : ¬ 2 ∣ ((Sgp153 T V₁ ⊓ L).subgroupOf L).index := hsylL.2.2
  have hodd : ¬ 2 ∣ ((L ⊓ Subgroup.centralizer ({v} : Set G)).subgroupOf L).index := by
    intro h2
    apply hB
    refine h2.trans (Subgroup.index_dvd_of_le ?_)
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hSLM x hx
  have hfixU : ∀ u ∈ ⁅centerOf (c134Q I L), L⁆,
      (∀ m ∈ L ⊓ Subgroup.centralizer ({v} : Set G), m * u * m⁻¹ = u) → u = 1 := by
    intro u hu hm
    by_contra hu1
    have hne : u ≠ u₀ := by
      intro h
      rw [h] at hm
      exact hy₀mv (hm y₀ (hYM y₀ hy₀))
    refine s8_no_two_fixed hF2 hmod.1 hU ((Sgp153 T V₁ ⊓ L).subgroupOf L) hB hu hu₀U hu1 hu₀1 hne
      ?_ ?_
    · intro b hb
      exact hm b (hSLM b (Subgroup.mem_subgroupOf.mp hb))
    · intro b hb
      have h := hu₀S b (Subgroup.mem_subgroupOf.mp hb).1
      calc (b : G) * u₀ * (b : G)⁻¹ = u₀ * b * (b : G)⁻¹ := by rw [h]
        _ = u₀ := by group
  obtain ⟨-, -, β, -, hβk, -⟩ := id hU
  have hεone : ∀ x ∈ L, ε x = 1 :=
    SzC4S8.cocycle_eq_one_of_odd_index
      (fun l hl => S153H.mem_normalizer_commutator (hLZ hl) (Subgroup.le_normalizer hl))
      (fun a ha b hb => hZab a (hUZ ha) b (hUZ hb))
      (fun a ha => s8_sq_eq_one_of_mem hF2 hβk ha) inf_le_left hodd hfixU ε hεU hcoc hεM
  have hvL : ∀ l ∈ L, l * v * l⁻¹ = v := by
    intro l hl
    have h := hεone l hl
    simp only [ε] at h
    exact (inv_mul_eq_one.mp h).symm
  have hvL' : ∀ l ∈ L, v * l = l * v := fun l hl => by
    calc v * l = (l * v * l⁻¹) * l := by rw [hvL l hl]
      _ = l * v := by group
  have hLV : L ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rcases hVall e he with rfl | rfl | rfl | rfl
    · simp
    · exact (hc₀L l hl).symm
    · exact hvL' l hl
    · calc c₀ * v * l = c₀ * (v * l) := by rw [mul_assoc]
        _ = c₀ * (l * v) := by rw [hvL' l hl]
        _ = (c₀ * l) * v := by rw [mul_assoc]
        _ = (l * c₀) * v := by rw [hc₀L l hl]
        _ = l * (c₀ * v) := by rw [mul_assoc]
  have hLM : L ≤ M := hLV.trans ((Subgroup.centralizer_le_normalizer _).trans c.c29.norm_le)
  exact c25.conc.2.1 (le_inf hLM hLI)

end Main

end CFSG.Quasithin.SzC4
