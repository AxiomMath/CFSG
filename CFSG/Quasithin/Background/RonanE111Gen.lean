module

public import CFSG.Quasithin.Background.RonanE111Cmod
public import CFSG.Quasithin.Background.RonanE111Semi
public import CFSG.Holt.General.Simple
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {Q : Type} [Group Q]

section Generation

theorem commutator_conj_mem_of_mem {H K : Subgroup Q} {x : Q} (hx : x ∈ H) {c : Q}
    (hc : c ∈ ⁅H, K⁆) : x * c * x⁻¹ ∈ ⁅H, K⁆ := by
  have key : ⁅H, K⁆ ≤ (⁅H, K⁆).comap (MulAut.conj x).toMonoidHom := by
    refine Subgroup.commutator_le.mpr fun d hd a ha => ?_
    show x * ⁅d, a⁆ * x⁻¹ ∈ ⁅H, K⁆
    have e : x * ⁅d, a⁆ * x⁻¹ = ⁅x * d, a⁆ * ⁅x, a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (⁅H, K⁆).mul_mem (Subgroup.commutator_mem_commutator (H.mul_mem hx hd) ha)
      ((⁅H, K⁆).inv_mem (Subgroup.commutator_mem_commutator hx ha))
  exact key hc

theorem conj_mem_sup_of {M₁ M₂ : Subgroup Q} {x : Q}
    (h₁ : ∀ c ∈ M₁, x * c * x⁻¹ ∈ M₁ ⊔ M₂) (h₂ : ∀ c ∈ M₂, x * c * x⁻¹ ∈ M₁ ⊔ M₂) {c : Q}
    (hc : c ∈ M₁ ⊔ M₂) : x * c * x⁻¹ ∈ M₁ ⊔ M₂ := by
  have key : M₁ ⊔ M₂ ≤ (M₁ ⊔ M₂).comap (MulAut.conj x).toMonoidHom :=
    sup_le (fun c hc => h₁ c hc) (fun c hc => h₂ c hc)
  exact key hc

theorem perfectCore_top_le_of_two_quotient [Finite Q] (N : Subgroup Q) [N.Normal]
    (h : ∀ y : Q, ∃ k : ℕ, y ^ 2 ^ k ∈ N) : perfectCore (⊤ : Subgroup Q) ≤ N := by
  have hP : IsPGroup 2 (Q ⧸ N) := by
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N g
    obtain ⟨k, hk⟩ := h y
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hk
  haveI : Group.IsNilpotent (Q ⧸ N) := hP.isNilpotent
  haveI : Group.IsSolvable (Q ⧸ N) := IsNilpotent.to_isSolvable
  have hbot : perfectCore (⊤ : Subgroup (Q ⧸ N)) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
  have hmap := map_perfectCore (QuotientGroup.mk' N) (⊤ : Subgroup Q)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), hbot] at hmap
  intro x hx
  have hxmem : QuotientGroup.mk' N x ∈ (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hx
  rw [hmap, Subgroup.mem_bot] at hxmem
  exact (QuotientGroup.eq_one_iff x).mp hxmem

theorem le_closure_commutators_of_swap {P : Type} [Group P] {L L' : Subgroup P} {a : P}
    (hL : IsSimpleGroup ↥L) (hnab : ∃ x y : ↥L, x * y ≠ y * x)
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (ha : A1b.conjSub a L = L') :
    L ≤ Subgroup.closure {u : P | ∃ x ∈ L, u = x * a * x⁻¹ * a⁻¹} := by
  set H := Subgroup.closure {u : P | ∃ x ∈ L, u = x * a * x⁻¹ * a⁻¹} with hHdef
  have hgen : ∀ x ∈ L, x * a * x⁻¹ * a⁻¹ ∈ H := fun x hx =>
    Subgroup.subset_closure ⟨x, hx, rfl⟩
  have hL' : ∀ x ∈ L, a * x * a⁻¹ ∈ L' := fun x hx => by
    rw [← ha]
    exact A1b.mem_conjSub_of_mem hx
  have hcomm_mem : ∀ x ∈ L, ∀ z ∈ L, x * z * x⁻¹ * z⁻¹ ∈ H := by
    intro x hx z hz
    have hw : x⁻¹ * z⁻¹ ∈ L := L.mul_mem (L.inv_mem hx) (L.inv_mem hz)
    have hX : a * x⁻¹ * a⁻¹ ∈ L' := hL' _ (L.inv_mem hx)
    have hZ : a * z⁻¹ * a⁻¹ ∈ L' := hL' _ (L.inv_mem hz)
    have hXZW : a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹) * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹) = 1 := by
      group
    have h1 : a * x⁻¹ * a⁻¹ * z = z * (a * x⁻¹ * a⁻¹) := (hcomm z hz _ hX).symm
    have h2 : a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹) * (x⁻¹ * z⁻¹) =
        x⁻¹ * z⁻¹ * (a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹)) :=
      (hcomm _ hw _ (L'.mul_mem hX hZ)).symm
    have E : x * (a * x⁻¹ * a⁻¹) * (z * (a * z⁻¹ * a⁻¹)) *
        (x⁻¹ * z⁻¹ * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)) = x * z * (x⁻¹ * z⁻¹) := by
      calc x * (a * x⁻¹ * a⁻¹) * (z * (a * z⁻¹ * a⁻¹)) *
            (x⁻¹ * z⁻¹ * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹))
          = x * (a * x⁻¹ * a⁻¹ * z) * (a * z⁻¹ * a⁻¹) *
            (x⁻¹ * z⁻¹ * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)) := by group
        _ = x * (z * (a * x⁻¹ * a⁻¹)) * (a * z⁻¹ * a⁻¹) *
            (x⁻¹ * z⁻¹ * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)) := by rw [h1]
        _ = x * z * ((a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹)) * (x⁻¹ * z⁻¹)) *
            (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹) := by group
        _ = x * z * (x⁻¹ * z⁻¹ * (a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹))) *
            (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹) := by rw [h2]
        _ = x * z * (x⁻¹ * z⁻¹) * (a * x⁻¹ * a⁻¹ * (a * z⁻¹ * a⁻¹) *
            (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)) := by group
        _ = x * z * (x⁻¹ * z⁻¹) := by rw [hXZW, mul_one]
    have key : x * a * x⁻¹ * a⁻¹ * (z * a * z⁻¹ * a⁻¹) *
        (x⁻¹ * z⁻¹ * a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹) = x * z * x⁻¹ * z⁻¹ := by
      calc x * a * x⁻¹ * a⁻¹ * (z * a * z⁻¹ * a⁻¹) *
            (x⁻¹ * z⁻¹ * a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)
          = x * (a * x⁻¹ * a⁻¹) * (z * (a * z⁻¹ * a⁻¹)) *
            (x⁻¹ * z⁻¹ * (a * (x⁻¹ * z⁻¹)⁻¹ * a⁻¹)) := by group
        _ = x * z * (x⁻¹ * z⁻¹) := E
        _ = x * z * x⁻¹ * z⁻¹ := by group
    rw [← key]
    exact H.mul_mem (H.mul_mem (hgen x hx) (hgen z hz)) (hgen _ hw)
  have hnorm : ((H ⊓ L).subgroupOf L).Normal := by
    refine normal_subgroupOf_of_conj inf_le_right fun g hg n hn => ?_
    have hX : a * g⁻¹ * a⁻¹ ∈ L' := hL' _ (L.inv_mem hg)
    have hcn : n * (a * g⁻¹ * a⁻¹) = a * g⁻¹ * a⁻¹ * n :=
      hcomm n (Subgroup.mem_inf.mp hn).2 _ hX
    have e : g * a * g⁻¹ * a⁻¹ * n * (g * a * g⁻¹ * a⁻¹)⁻¹ = g * n * g⁻¹ := by
      calc g * a * g⁻¹ * a⁻¹ * n * (g * a * g⁻¹ * a⁻¹)⁻¹
          = g * (a * g⁻¹ * a⁻¹ * n) * (a * g⁻¹ * a⁻¹)⁻¹ * g⁻¹ := by group
        _ = g * (n * (a * g⁻¹ * a⁻¹)) * (a * g⁻¹ * a⁻¹)⁻¹ * g⁻¹ := by rw [← hcn]
        _ = g * n * g⁻¹ := by group
    rw [Subgroup.mem_inf]
    refine ⟨?_, L.mul_mem (L.mul_mem hg (Subgroup.mem_inf.mp hn).2) (L.inv_mem hg)⟩
    rw [← e]
    exact H.mul_mem (H.mul_mem (hgen g hg) (Subgroup.mem_inf.mp hn).1) (H.inv_mem (hgen g hg))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((H ⊓ L).subgroupOf L) with hbot | htop
  · exfalso
    obtain ⟨x, z, hxz⟩ := hnab
    have hc : (x : P) * z * (x : P)⁻¹ * (z : P)⁻¹ ∈ H ⊓ L :=
      Subgroup.mem_inf.mpr ⟨hcomm_mem _ x.2 _ z.2,
        L.mul_mem (L.mul_mem (L.mul_mem x.2 z.2) (L.inv_mem x.2)) (L.inv_mem z.2)⟩
    have hmem : x * z * x⁻¹ * z⁻¹ ∈ (H ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hc
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : (x : P) * z * (x : P)⁻¹ * (z : P)⁻¹ = 1 := by
      have := congrArg Subtype.val hmem
      simpa using this
    apply hxz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (x : P) * z = ((x : P) * z * (x : P)⁻¹ * (z : P)⁻¹) * ((z : P) * (x : P)) := by group
      _ = (z : P) * (x : P) := by rw [h2, one_mul]
  · exact (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_left

theorem D_le_commutator_sup {T₀ D Y A : Subgroup Q} {𝒟 : Set (Subgroup Q)} [Y.Normal] [D.Normal]
    (hAab : IsElemAbelian 2 A) (hAT₀ : A ≤ T₀) (hT₀A : ∀ t ∈ T₀, ∀ a ∈ A, t * a = a * t)
    (hSM : SemisimpleMod T₀ D Y 𝒟) (hmove : ∃ S ∈ 𝒟, ¬ A ≤ Cmod S Y) : D ≤ ⁅D, A⁆ ⊔ Y := by
  have hconjT : ∀ t ∈ T₀, ∀ c ∈ ⁅D, A⁆, t * c * t⁻¹ ∈ ⁅D, A⁆ := by
    intro t ht
    have key : ⁅D, A⁆ ≤ (⁅D, A⁆).comap (MulAut.conj t).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun d hd a ha => ?_
      have hta : MulAut.conj t a = a := by
        show t * a * t⁻¹ = a
        rw [hT₀A t ht a ha]
        group
      show MulAut.conj t ⁅d, a⁆ ∈ ⁅D, A⁆
      rw [map_commutatorElement, hta]
      exact Subgroup.commutator_mem_commutator (Subgroup.Normal.conj_mem ‹D.Normal› d hd t) ha
    intro c hc
    exact key hc
  have hMconj : ∀ t ∈ T₀, ∀ c ∈ ⁅D, A⁆ ⊔ Y, t * c * t⁻¹ ∈ ⁅D, A⁆ ⊔ Y := fun t ht c hc =>
    conj_mem_sup_of (x := t) (fun c' hc' => Subgroup.mem_sup_left (hconjT t ht c' hc'))
      (fun y hy => Subgroup.mem_sup_right (Subgroup.Normal.conj_mem ‹Y.Normal› y hy t)) hc
  obtain ⟨S₀, hS₀, hS₀nc⟩ := hmove
  have hS₀D : S₀ ≤ D := hSM.le_D S₀ hS₀
  have hYS₀ : Y ≤ S₀ := hSM.Y_le S₀ hS₀
  have hS₀M : S₀ ≤ ⁅D, A⁆ ⊔ Y := by
    by_cases hA1 : ∀ a ∈ A, A1b.conjSub a S₀ = S₀
    ·
      have hcS : ⁅S₀, A⁆ ≤ S₀ := by
        refine Subgroup.commutator_le.mpr fun s hs a ha => ?_
        have h1 : a * s⁻¹ * a⁻¹ ∈ S₀ := by
          have h2 : a * s⁻¹ * a⁻¹ ∈ A1b.conjSub a S₀ :=
            A1b.mem_conjSub_of_mem (S₀.inv_mem hs)
          rwa [hA1 a ha] at h2
        have h3 := S₀.mul_mem hs h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using h3
      have hN : ⁅S₀, A⁆ ⊔ Y ≤ S₀ := sup_le hcS hYS₀
      have hNn : ((⁅S₀, A⁆ ⊔ Y).subgroupOf S₀).Normal := by
        refine normal_subgroupOf_of_conj hN fun s hs n hn => ?_
        exact conj_mem_sup_of (x := s)
          (fun c hc => Subgroup.mem_sup_left (commutator_conj_mem_of_mem hs hc))
          (fun y hy => Subgroup.mem_sup_right (Subgroup.Normal.conj_mem ‹Y.Normal› y hy s)) hn
      rcases hSM.simple S₀ hS₀ (⁅S₀, A⁆ ⊔ Y) le_sup_right hN hNn with hY | hS
      ·
        exfalso
        apply hS₀nc
        have hcY : ⁅S₀, A⁆ ≤ Y := le_trans le_sup_left hY.le
        intro a ha
        rw [mem_Cmod_iff]
        intro s hs
        have h1 : s * a * s⁻¹ * a⁻¹ ∈ Y := hcY (Subgroup.commutator_mem_commutator hs ha)
        have h2 := Y.inv_mem h1
        have e : (s * a * s⁻¹ * a⁻¹)⁻¹ = a * s * a⁻¹ * s⁻¹ := by group
        rwa [e] at h2
      · calc S₀ = ⁅S₀, A⁆ ⊔ Y := hS.symm
          _ ≤ ⁅D, A⁆ ⊔ Y := sup_le_sup_right (Subgroup.commutator_mono hS₀D le_rfl) Y
    ·
      push Not at hA1
      obtain ⟨a, haA, hne⟩ := hA1
      have hS'mem : A1b.conjSub a S₀ ∈ 𝒟 := hSM.conj S₀ hS₀ a (hAT₀ haA)
      have hcomm0 : ⁅S₀, A1b.conjSub a S₀⁆ ≤ Y := hSM.comm S₀ hS₀ _ hS'mem (Ne.symm hne)
      have hL : IsSimpleGroup ↥(S₀.map (QuotientGroup.mk' Y)) :=
        isSimpleGroup_map_of_le hYS₀ (hSM.simple S₀ hS₀) (hSM.nonab S₀ hS₀)
      have hnab : ∃ x y : ↥(S₀.map (QuotientGroup.mk' Y)), x * y ≠ y * x :=
        nonabelian_map_of_not_le (hSM.nonab S₀ hS₀)
      have hcomm : ∀ x ∈ S₀.map (QuotientGroup.mk' Y),
          ∀ y ∈ (A1b.conjSub a S₀).map (QuotientGroup.mk' Y), x * y = y * x := by
        rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
        have hc : ⁅s, s'⁆ ∈ Y := hcomm0 (Subgroup.commutator_mem_commutator hs hs')
        have h1 : QuotientGroup.mk' Y (s * s' * s⁻¹ * s'⁻¹) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr (by simpa [commutatorElement_def] using hc)
        simp only [map_mul, map_inv] at h1
        have h2 : (QuotientGroup.mk' Y s) * (QuotientGroup.mk' Y s') =
            (QuotientGroup.mk' Y s') * (QuotientGroup.mk' Y s) := by
          have := congrArg (fun z => z * (QuotientGroup.mk' Y s') * (QuotientGroup.mk' Y s)) h1
          simpa [mul_assoc] using this
        exact h2
      have ha_conj : A1b.conjSub (QuotientGroup.mk' Y a) (S₀.map (QuotientGroup.mk' Y)) =
          (A1b.conjSub a S₀).map (QuotientGroup.mk' Y) :=
        (E1.map_conjSub (QuotientGroup.mk' Y) a S₀).symm
      have hsw := le_closure_commutators_of_swap hL hnab hcomm ha_conj
      have hclos : Subgroup.closure {u : Q ⧸ Y | ∃ x ∈ S₀.map (QuotientGroup.mk' Y),
          u = x * QuotientGroup.mk' Y a * x⁻¹ * (QuotientGroup.mk' Y a)⁻¹} ≤
          (⁅D, A⁆).map (QuotientGroup.mk' Y) := by
        rw [Subgroup.closure_le]
        rintro u ⟨x, hx, rfl⟩
        obtain ⟨s, hs, rfl⟩ := hx
        refine Subgroup.mem_map.mpr ⟨⁅s, a⁆, Subgroup.commutator_mem_commutator (hS₀D hs) haA, ?_⟩
        simp only [commutatorElement_def, map_mul, map_inv]
      have hLle : S₀.map (QuotientGroup.mk' Y) ≤ (⁅D, A⁆).map (QuotientGroup.mk' Y) :=
        hsw.trans hclos
      intro s hs
      obtain ⟨c, hc, hcs⟩ := hLle (Subgroup.mem_map_of_mem _ hs)
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hcs
      have hcs' : c⁻¹ * s ∈ Y := QuotientGroup.eq.mp hcs
      have key : c * (c⁻¹ * s) ∈ ⁅D, A⁆ ⊔ Y :=
        (⁅D, A⁆ ⊔ Y).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hcs')
      have e : c * (c⁻¹ * s) = s := by group
      rwa [e] at key
  refine (le_of_eq hSM.gen.symm).trans (iSup₂_le fun S hS => ?_)
  obtain ⟨t, ht, rfl⟩ := hSM.trans S₀ hS₀ S hS
  intro y hy
  rw [A1b.mem_conjSub_iff] at hy
  have h := hMconj t ht _ (hS₀M hy)
  have e : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
  rwa [e] at h

theorem eq_commutator_of_le_sup [Finite Q] {D Y A : Subgroup Q} [Y.Normal] [D.Normal]
    (hDperf : ⁅D, D⁆ = D) (hYD : Y ≤ D) (hYs : Group.IsSolvable ↥Y) (hle : D ≤ ⁅D, A⁆ ⊔ Y) :
    D = ⁅D, A⁆ := by
  have hCD : ⁅D, A⁆ ≤ D := by
    refine Subgroup.commutator_le.mpr fun d hd a _ => ?_
    rw [commutatorElement_def]
    have h1 : a * d⁻¹ * a⁻¹ ∈ D := Subgroup.Normal.conj_mem ‹D.Normal› d⁻¹ (D.inv_mem hd) a
    simpa [mul_assoc] using D.mul_mem hd h1
  have hnorm : ((⁅D, A⁆).subgroupOf D).Normal :=
    normal_subgroupOf_of_conj hCD fun s hs n hn => commutator_conj_mem_of_mem hs hn
  have hsup : D = ⁅D, A⁆ ⊔ Y := le_antisymm hle (sup_le hCD hYD)
  have h1 : perfectCore D ≤ ⁅D, A⁆ := perfectCore_le_of_sup_solvable hCD hnorm hsup hYs
  have h2 : D ≤ ⁅D, A⁆ := (perfectCore_eq_self_of_perfect hDperf).symm.le.trans h1
  exact le_antisymm h2 hCD

theorem twoResidual_top_of_perfect [Finite Q] {D T₀ : Subgroup Q} [D.Normal]
    (hDperf : ⁅D, D⁆ = D) (hT₀ : IsPGroup 2 T₀) (hDT₀ : D ⊔ T₀ = ⊤) :
    twoResidual (⊤ : Subgroup Q) = D ∧ perfectCore (⊤ : Subgroup Q) = D := by
  have hexp : ∀ y : Q, ∃ k : ℕ, y ^ 2 ^ k ∈ D := by
    intro y
    have hy : y ∈ D ⊔ T₀ := hDT₀ ▸ Subgroup.mem_top y
    obtain ⟨d, hd, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
    obtain ⟨k, hk⟩ := hT₀ ⟨t, ht⟩
    have ht' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ?_⟩
    have hd1 : QuotientGroup.mk' D d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    have hmk : QuotientGroup.mk' D (d * t) = QuotientGroup.mk' D t := by
      rw [map_mul, hd1, one_mul]
    have h1 : QuotientGroup.mk' D ((d * t) ^ 2 ^ k) = 1 := by
      rw [map_pow, hmk, ← map_pow, ht', map_one]
    rw [QuotientGroup.mk'_apply] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hpc : perfectCore (⊤ : Subgroup Q) = D := by
    refine le_antisymm ?_ (le_perfectCore_of_perfect le_top hDperf)
    have hBs : Group.IsSolvable ↥T₀ := by
      haveI : Group.IsNilpotent ↥T₀ := hT₀.isNilpotent
      exact IsNilpotent.to_isSolvable
    exact perfectCore_le_of_sup_solvable (A := D) (B := T₀) (Y := ⊤) le_top
      (normal_subgroupOf_of_conj le_top fun s _ n hn =>
        Subgroup.Normal.conj_mem ‹D.Normal› n hn s)
      hDT₀.symm hBs
  have hle : twoResidual (⊤ : Subgroup Q) ≤ D := by
    refine twoResidual_le_of_isTwoQuotient le_top ?_ (fun y _ => hexp y)
    exact (Subgroup.normalizer_eq_top_iff.mpr inferInstance).symm.le
  have hge : D ≤ twoResidual (⊤ : Subgroup Q) := by
    rw [← hpc]
    intro x hx
    rw [mem_twoResidual_iff]
    intro N _ h2 h3
    haveI : N.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h2)
    exact perfectCore_top_le_of_two_quotient N (fun y => h3 y (Subgroup.mem_top y)) hx
  exact ⟨le_antisymm hle hge, hpc⟩

theorem exists_involution_of_isComp [Finite Q] {X S : Subgroup Q} (hS : IsComp X S) :
    ∃ x ∈ S, x ≠ 1 ∧ x ^ 2 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup ↥S := hS.2.2.1
  have h2 : Even (Nat.card ↥S) := CFSG.Holt.General.even_card_of_isSimpleGroup hS.2.2.2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥S) 2 (even_iff_two_dvd.mp h2)
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  refine ⟨(t : Q), t.2, fun h => ht1 (Subtype.ext h), ?_⟩
  have h3 := congrArg Subtype.val ht2
  simpa using h3

end Generation

end CFSG.Quasithin.RonanE111
