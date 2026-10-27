
module

public import CFSG.Quasithin.Recognition.L34AmalgamDataBase
public meta import CFSG.Quasithin.Recognition.L34AmalgamDataBase
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

@[expose] def tab (g : M22) : Array (Fin 22) := Array.ofFn fun x => (g : Equiv.Perm (Fin 22)) x

@[expose] def bWords : List String :=
  ["", "R", "p", "q", "r", "Rp", "Rq", "pR", "pq", "pr", "qR", "qp", "qr", "rp", "rq", "Rpq",
   "Rpr", "Rqp", "Rqr", "pRp", "pRq", "pqR", "pqp", "pqr", "prp", "prq", "qRp", "qRq", "qpR",
   "qpq", "qpr", "qrp", "qrq", "rpR", "rpq", "rqR", "rqp", "RpqR", "Rpqp", "Rpqr", "Rprq",
   "RqpR", "Rqpq", "Rqpr", "Rqrp", "pRpq", "pRqp", "pRqr", "pqRp", "pqRq", "pqpR", "pqpq",
   "pqpr", "pqrp", "pqrq", "prpq", "prqR", "prqp", "qRpq", "qRpr", "qRqp", "qpRp", "qpRq",
   "qpqR", "qpqr", "qprp", "qprq", "qrpR", "qrpq", "qrqp", "rpRq", "rpqR", "rpqp", "rpqr",
   "rqRp", "rqpR", "rqpq", "rqpr", "RpqRq", "RpqpR", "Rpqpq", "Rpqpr", "RprqR", "Rprqp", "RqpRp",
   "RqpqR", "Rqpqr", "RqrpR", "Rqrpq", "pRpqR", "pRpqp", "pRpqr", "pRqpq", "pRqpr", "pRqrp",
   "pqRpr", "pqRqp", "pqpRp", "pqpRq", "pqpqR", "pqpqr", "pqprp", "pqprq", "pqrpR", "pqrqp",
   "prpqR", "prpqp", "prpqr", "prqRp", "prqpR", "prqpq", "qRpqp", "qRprq", "qRqpR", "qRqpq",
   "qRqpr", "qpRpq", "qpRqr", "qpqRp", "qpqRq", "qpqrp", "qpqrq", "qprpq", "qprqR", "qrpRq",
   "qrpqp", "qrqpR", "qrqpq", "qrqpr", "rpRqp", "rpRqr", "rpqRp", "rpqpR", "rpqpq", "rpqpr",
   "rpqrq", "rqRpq", "rqRpr", "rqpRq", "rqpqR", "rqpqr", "rqprp", "RpqRqp", "RpqpqR", "Rpqpqr",
   "RqpRpq", "pRpqpR", "pRpqpq", "pRqpqR", "pRqrpR", "pqRqpR", "pqRqpq", "pqRqpr", "pqpRpq",
   "pqpRqr", "pqpqRp", "pqpqRq", "pqpqrp", "pqpqrq", "pqprpq", "pqprqR", "pqrqpR", "pqrqpq",
   "pqrqpr", "prpqRp", "prpqpq", "prpqpr", "prqRpr", "prqpRq", "prqpqr", "qRpqpq", "qpRpqR",
   "qpqRpr", "qpqRqp", "qpqrpR", "qpqrqp", "qprpqr", "qrpqpq", "rpRqrp", "rpqpqR", "rpqpqr",
   "rpqprq", "rpqrqp", "rqRprq", "rqpqrp", "rqprpq", "pRpqpqr", "prpqpqR", "qRpqpqr", "qrpqpqR",
   "rpqrqpr", "rqprpqr"]

@[expose] def bTabs : List (Array (Fin 22)) := bWords.map fun s => tab (evalW gen (word s))

end CFSG.Quasithin.L34Amalgam
