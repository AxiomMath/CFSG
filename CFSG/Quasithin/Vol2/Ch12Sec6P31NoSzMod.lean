module

public import CFSG.Quasithin.Background.F918P5
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.H13.A6S13816Sz
public import CFSG.Quasithin.Vol2.Ch12Sec6P31NoSzSkel
public import CFSG.Quasithin.Vol2.Ch12Sec6P31a

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31

section Act

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

attribute [local instance] commGroupOfFact

@[expose] noncomputable def rhoQ [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    HStar H →* MulAut ↥(tildeOf V₁ (conjClosure I H)) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥H)
    (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) (fun x hx =>
      h.actH_eq_one_of_mem_pCoreOf hIU ((CFSG.mem_openPCoreOf_iff x).2 hx))

theorem rhoQ_mk [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (x : ↥H) :
    rhoQ h hIU (QuotientGroup.mk x) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x := rfl

@[expose] def iotaQ (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    ↥(tildeOf V₁ (conjClosure I H)) → ↥(UT V₁ Vp H) :=
  Subgroup.inclusion (secImg_mono (conjClosure_le_conjClosure_U hIU le_rfl))

theorem iotaQ_injective (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    Function.Injective (iotaQ h hIU) := Subgroup.inclusion_injective _

theorem iotaQ_one (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    iotaQ h hIU 1 = 1 := rfl

theorem psiH_iotaQ [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (y : HStar H)
    (q : ↥(tildeOf V₁ (conjClosure I H))) :
    psiH h.toHypF98.toHypF91 y (iotaQ h hIU q) = iotaQ h hIU (rhoQ h hIU y q) := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    apply Subtype.ext
    rw [rhoQ_mk, psiH_mk, thetaH_apply]
    show _ = ((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x q :
      ↥(tildeOf V₁ (conjClosure I H))) : SecQuot (N1 V₁) V₁)
    rw [actH_apply_coe]
    rfl

theorem mem_autIH_iff [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hKK : conjClosure K T = K)
    (x : MulAut ↥(tildeOf V₁ (conjClosure I H))) :
    x ∈ autIH V₁ I H (conjClosure K T) ↔ ∃ n ∈ star H K, rhoQ h hIU n = x := by
  rw [autIH_eq_map h h.K₀_le_H, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨QuotientGroup.mk k, ⟨k, ?_, rfl⟩, rfl⟩
    rw [← hKK]
    exact Subgroup.mem_subgroupOf.1 hk
  · rintro ⟨n, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨k, Subgroup.mem_subgroupOf.2 ?_, rfl⟩
    rw [hKK]
    exact Subgroup.mem_subgroupOf.1 hk

theorem rhoQ_mem_subM [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnorm : H ≤ Subgroup.normalizer (I : Set G)) (y : HStar H)
    {m : ↥(tildeOf V₁ (conjClosure I H))} (hm : m ∈ subM V₁ (conjClosure I H) I) :
    rhoQ h hIU y m ∈ subM V₁ (conjClosure I H) I := by
  induction y using QuotientGroup.induction_on with
  | H x =>
    rw [mem_subM_iff] at hm ⊢
    rw [rhoQ_mk, actH_apply_coe]
    exact secMk_conj_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := I)
      (a := ⟨x, h.H_le_normalizer_V₁ x.2⟩) (hnorm x.2) hm

end Act

section Main

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

attribute [local instance] commGroupOfFact

theorem false_of_normalizer [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hSzE : A6.SzEnd) (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hirr : IsIrrPlusTildeT h hIU) (hKK : conjClosure K T = K)
    (hnorm : H ≤ Subgroup.normalizer (I : Set G)) {f : ℕ}
    (hnat : BinaryNaturalSz (autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)
      (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) f)
    (E : Subgroup (HStar H)) (hE3 : ∀ e ∈ E, ∃ k : ℕ, e ^ 3 ^ k = 1)
    (hEC : E ≤ Subgroup.centralizer (star H K : Set (HStar H)))
    (hfpf : ∀ w : ↥(UT V₁ Vp H), (∀ e ∈ E, psiH h.toHypF98.toHypF91 e w = w) → w = 1) : False := by
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirr
  obtain ⟨⟨-, -, hcomm, hCM, -⟩, -⟩ := hirr'
  set M : Subgroup ↥(tildeOf V₁ (conjClosure I H)) := subM V₁ (conjClosure I H) I with hM
  set C : Subgroup ↥(tildeOf V₁ (conjClosure I H)) :=
    XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) M with hC
  have hX := mem_autIH_iff h hIU hKK
  have hcommE : ∀ e ∈ E, ∀ m ∈ autIH V₁ I H (conjClosure K T),
      rhoQ h hIU e * m = m * rhoQ h hIU e := by
    intro e he m hm
    obtain ⟨n, hn, rfl⟩ := (hX m).1 hm
    have hcn := Subgroup.mem_centralizer_iff.1 (hEC he) n hn
    rw [← map_mul, ← map_mul, hcn]
  have hscalar : ∀ e ∈ E, ∀ m ∈ M, rhoQ h hIU e m * m⁻¹ ∈ C := by
    intro e he
    have hcU : ∀ u ∈ M, rhoQ h hIU e u ∈ M := fun u hu => rhoQ_mem_subM h hIU hnorm e hu
    have hcC : ∀ u ∈ C, rhoQ h hIU e u ∈ C := by
      intro u hu
      refine ⟨hcU u hu.1, fun a => ?_⟩
      have e1 : (a : MulAut _) (rhoQ h hIU e u) = rhoQ h hIU e ((a : MulAut _) u) := by
        have := congrArg (fun ψ : MulAut _ => ψ u) (hcommE e he a a.2)
        simpa [MulAut.mul_apply] using this.symm
      have hu' := hu.2 a
      rw [Subgroup.smul_def, MulAut.smul_def] at hu' ⊢
      rw [e1, hu']
    exact hSzE _ _ _ _ f hnat (rhoQ h hIU e)
      (by
        obtain ⟨k, hk⟩ := hE3 e he
        exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
      hcU hcC (hcommE e he)
  have hEtriv : ∀ e ∈ E, ∀ m ∈ M, rhoQ h hIU e m = m := by
    intro e he
    refine P31Sz.trivial_of_head (rhoQ h hIU) (star H K) e ?_ M C
      (fun k hk m hm => rhoQ_mem_subM h hIU hnorm k hm) ?_
      (fun k hk c hc => hc.2 ⟨rhoQ h hIU k, (hX _).2 ⟨k, hk, rfl⟩⟩) (hscalar e he)
    · intro k hk
      exact (Subgroup.mem_centralizer_iff.1 (hEC he) k hk).symm
    · intro m hm
      have hm' : m ∈ XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) M := by rw [hcomm]; exact hm
      refine Subgroup.closure_mono ?_ hm'
      rintro c ⟨x, l, hl, rfl⟩
      obtain ⟨n, hn, hnx⟩ := (hX x.1).1 x.2
      exact ⟨n, hn, l, hl, by
        show ((x : MulAut ↥(tildeOf V₁ (conjClosure I H))) l) * l⁻¹ = (rhoQ h hIU n) l * l⁻¹
        rw [← hnx]⟩
  obtain ⟨m₀, hm₀M, hm₀C⟩ := SetLike.exists_of_lt hCM
  have hm₀1 : m₀ ≠ 1 := fun h1 => hm₀C (by rw [h1]; exact C.one_mem)
  have hfix := hfpf (iotaQ h hIU m₀) (fun e he => by
    rw [psiH_iotaQ h hIU, hEtriv e he m₀ hm₀M])
  exact hm₀1 (iotaQ_injective h hIU (hfix.trans (iotaQ_one h hIU).symm))

end Main


end CFSG.Quasithin.H13.P31Sz
